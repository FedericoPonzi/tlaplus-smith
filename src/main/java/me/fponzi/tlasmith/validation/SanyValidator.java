package me.fponzi.tlasmith.validation;

import me.fponzi.tlasmith.ast.Spec;
import org.apache.commons.io.output.WriterOutputStream;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import util.SimpleFilenameToStream;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

public class SanyValidator {

    public static class ValidationResult {
        private final boolean valid;
        private final List<String> errors;
        private final List<String> warnings;

        public ValidationResult(boolean valid, List<String> errors, List<String> warnings) {
            this.valid = valid;
            this.errors = new ArrayList<>(errors);
            this.warnings = new ArrayList<>(warnings);
        }

        public boolean isValid() {
            return valid;
        }

        public List<String> getErrors() {
            return new ArrayList<>(errors);
        }

        public List<String> getWarnings() {
            return new ArrayList<>(warnings);
        }

        public boolean hasErrors() {
            return !errors.isEmpty();
        }

        public boolean hasWarnings() {
            return !warnings.isEmpty();
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append("ValidationResult{valid=").append(valid);
            if (hasErrors()) {
                sb.append(", errors=").append(errors.size());
            }
            if (hasWarnings()) {
                sb.append(", warnings=").append(warnings.size());
            }
            sb.append("}");
            return sb.toString();
        }

        public static ValidationResult valid() {
            return new ValidationResult(true, new ArrayList<>(), new ArrayList<>());
        }

        public static ValidationResult invalid(String error) {
            List<String> errors = new ArrayList<>();
            errors.add(error);
            return new ValidationResult(false, errors, new ArrayList<>());
        }

        public static ValidationResult withWarning(String warning) {
            List<String> warnings = new ArrayList<>();
            warnings.add(warning);
            return new ValidationResult(true, new ArrayList<>(), warnings);
        }
    }

    public ValidationResult validate(Spec spec) {
        return validateTLAText(spec.toTLAString());
    }

    public ValidationResult validateTLAText(String tlaText) {
        try {
            return validateWithSany(tlaText);
        } catch (Exception e) {
            return ValidationResult.invalid("SANY validation failed: " + e.getMessage());
        }
    }

    private ValidationResult validateWithSany(String tlaText) throws IOException {
        List<String> errors = new ArrayList<>();
        List<String> warnings = new ArrayList<>();

        // Basic validation checks first
        if (tlaText == null || tlaText.trim().isEmpty()) {
            errors.add("TLA+ specification is empty");
            return new ValidationResult(false, errors, warnings);
        }

        if (!tlaText.contains("---- MODULE") || !tlaText.contains("====")) {
            errors.add("Invalid TLA+ module structure");
            return new ValidationResult(false, errors, warnings);
        }

        // Extract module name for temp file
        String moduleName = extractModuleName(tlaText);

        // Write TLA+ text to temporary file with proper name
        File tempFile = null;
        try {
            File tempDir = Files.createTempDirectory("tlasmith").toFile();
            tempFile = new File(tempDir, moduleName + ".tla");
            try (FileWriter writer = new FileWriter(tempFile)) {
                writer.write(tlaText);
            }

            // Validate using SANY
            try {
                validateFileWithSany(tempFile);
                return ValidationResult.valid();
            } catch (SanySyntaxException e) {
                errors.add("Syntax error: " + e.getMessage());
                return new ValidationResult(false, errors, warnings);
            } catch (SanySemanticException e) {
                errors.add("Semantic error: " + e.getMessage());
                return new ValidationResult(false, errors, warnings);
            } catch (SanyFrontendException e) {
                errors.add("Frontend error: " + e.getMessage());
                return new ValidationResult(false, errors, warnings);
            } catch (SanyException e) {
                errors.add("SANY error: " + e.getMessage());
                return new ValidationResult(false, errors, warnings);
            }

        } finally {
            if (tempFile != null && tempFile.exists()) {
                tempFile.delete();
                // Also clean up parent temp directory
                File parentDir = tempFile.getParentFile();
                if (parentDir != null && parentDir.exists()) {
                    parentDir.delete();
                }
            }
        }
    }

    private void validateFileWithSany(File file) throws IOException, SanyFrontendException {
        var errBuf = new StringWriter();

        // Set a unique tmpdir to avoid race-condition in SANY
        File tempDir = Files.createTempDirectory("sanyimp").toFile();
        System.setProperty("java.io.tmpdir", tempDir.toString());

        try {
            var filenameResolver = new SimpleFilenameToStream(file.getAbsoluteFile().getParent());
            var specObj = new SpecObj(file.getAbsolutePath(), filenameResolver);

            var outStream = WriterOutputStream
                    .builder()
                    .setWriter(errBuf)
                    .setCharset(StandardCharsets.UTF_8)
                    .get();

            try {
                SANY.frontEndMain(
                        specObj,
                        file.getAbsolutePath(),
                        new PrintStream(outStream)
                );
            } catch (FrontEndException e) {
                throw new SanyFrontendException(e);
            }

            throwOnError(specObj);
        } finally {
            // Clean up temp directory
            if (tempDir.exists()) {
                tempDir.delete();
            }
        }
    }

    private void throwOnError(SpecObj specObj) {
        var parseErrors = specObj.getParseErrors();
        if (parseErrors.isFailure()) {
            throw new SanySyntaxException(parseErrors.toString());
        }

        var semanticErrors = specObj.getSemanticErrors();
        if (semanticErrors.isFailure()) {
            throw new SanySemanticException(semanticErrors.toString());
        }

        // the error level is above zero, so SANY failed for an unknown reason
        if (specObj.getErrorLevel() > 0) {
            throw new SanyException(
                    String.format("Unknown SANY error (error level=%d)", specObj.getErrorLevel())
            );
        }
    }

    public boolean isAvailable() {
        return true; // Now that we have SANY integrated
    }

    public String getSanyVersion() {
        return "TLA2Tools 1.8.0-SNAPSHOT";
    }

    private String extractModuleName(String tlaText) {
        // Extract module name from "---- MODULE ModuleName ----"
        String[] lines = tlaText.split("\n");
        for (String line : lines) {
            if (line.trim().startsWith("---- MODULE")) {
                String[] parts = line.trim().split("\\s+");
                if (parts.length >= 3) {
                    return parts[2]; // "----", "MODULE", "ModuleName", "----"
                }
            }
        }
        return "UnknownModule"; // fallback
    }
}
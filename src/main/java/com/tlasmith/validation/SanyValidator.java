package com.tlasmith.validation;

import com.tlasmith.ast.Spec;

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
        // TODO: Integrate with actual SANY parser
        // For now, perform basic syntactic checks

        List<String> errors = new ArrayList<>();
        List<String> warnings = new ArrayList<>();

        // Basic validation checks
        if (tlaText == null || tlaText.trim().isEmpty()) {
            errors.add("TLA+ specification is empty");
        }

        if (!tlaText.contains("---- MODULE") || !tlaText.contains("====")) {
            errors.add("Invalid TLA+ module structure");
        }

        // Check for common syntax issues
        if (tlaText.contains("VARIABLES") && !tlaText.contains("Init")) {
            warnings.add("Specification has variables but no Init formula");
        }

        if (tlaText.contains("Init") && !tlaText.contains("Next")) {
            warnings.add("Specification has Init but no Next formula");
        }

        // Check for balanced parentheses
        if (!hasBalancedParentheses(tlaText)) {
            errors.add("Unbalanced parentheses in specification");
        }

        boolean isValid = errors.isEmpty();
        return new ValidationResult(isValid, errors, warnings);
    }

    private boolean hasBalancedParentheses(String text) {
        int count = 0;
        for (char c : text.toCharArray()) {
            if (c == '(') {
                count++;
            } else if (c == ')') {
                count--;
                if (count < 0) {
                    return false;
                }
            }
        }
        return count == 0;
    }

    public boolean isAvailable() {
        // TODO: Check if SANY is available in the system
        // For now, return false since this is just a stub
        return false;
    }

    public String getSanyVersion() {
        // TODO: Return actual SANY version when integrated
        return "SANY integration not available";
    }

    // Placeholder methods for future SANY integration

    public ValidationResult validateWithFullSany(String tlaText) {
        if (!isAvailable()) {
            return ValidationResult.invalid("SANY not available");
        }

        // TODO: Implement actual SANY integration
        // This would involve:
        // 1. Writing TLA+ text to temporary file
        // 2. Calling SANY parser via command line or Java API
        // 3. Parsing SANY output for errors and warnings
        // 4. Returning structured ValidationResult

        throw new UnsupportedOperationException("Full SANY integration not yet implemented");
    }

    public void setSanyPath(String path) {
        // TODO: Set path to SANY installation
        throw new UnsupportedOperationException("SANY path configuration not yet implemented");
    }
}
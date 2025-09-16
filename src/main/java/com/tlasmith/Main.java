package com.tlasmith;

import com.tlasmith.ast.Spec;
import com.tlasmith.generator.Generator;
import com.tlasmith.printer.TLAPrinter;
import com.tlasmith.validation.SanyValidator;

public class Main {
    public static void main(String[] args) {
        System.out.println("TLA+-Smith: Random TLA+ Specification Generator");
        System.out.println("============================================");
        System.out.println();

        // Parse command line arguments
        int numSpecs = 3;
        long seed = System.currentTimeMillis();

        if (args.length > 0) {
            try {
                numSpecs = Integer.parseInt(args[0]);
            } catch (NumberFormatException e) {
                System.err.println("Warning: Invalid number of specs, using default: " + numSpecs);
            }
        }

        if (args.length > 1) {
            try {
                seed = Long.parseLong(args[1]);
            } catch (NumberFormatException e) {
                System.err.println("Warning: Invalid seed, using default: " + seed);
            }
        }

        System.out.println("Generating " + numSpecs + " TLA+ specifications with seed: " + seed);
        System.out.println();

        // Create generator with specific seed for reproducibility
        Generator generator = new Generator(seed);
        SanyValidator validator = new SanyValidator();

        // Generate and display specifications
        for (int i = 1; i <= numSpecs; i++) {
            System.out.println("=== Specification " + i + " ===");

            String moduleName = "RandomSpec" + i;
            Spec spec = generator.generateSpec(moduleName);

            // Print the specification
            String tlaText = TLAPrinter.print(spec);
            System.out.println(tlaText);
            System.out.println();

            // Validate the specification
            SanyValidator.ValidationResult result = validator.validateTLAText(tlaText);
            System.out.println("Validation: " + (result.isValid() ? "VALID" : "INVALID"));

            if (result.hasErrors()) {
                System.out.println("Errors:");
                for (String error : result.getErrors()) {
                    System.out.println("  - " + error);
                }
            }

            if (result.hasWarnings()) {
                System.out.println("Warnings:");
                for (String warning : result.getWarnings()) {
                    System.out.println("  - " + warning);
                }
            }

            System.out.println();
        }

        // Display generator statistics
        displayGeneratorInfo(generator);

        // Display validation info
        System.out.println("SANY Integration:");
        System.out.println("  Available: " + validator.isAvailable());
        System.out.println("  Version: " + validator.getSanyVersion());
        System.out.println();

        System.out.println("Generation complete!");
    }

    private static void displayGeneratorInfo(Generator generator) {
        System.out.println("Generator Configuration:");
        System.out.println("  Using default configuration");
        System.out.println("  Max depth: 4");
        System.out.println("  Variables: 2-5 per spec");
        System.out.println("  Constants: 1-3 per spec");
        System.out.println();
    }

    public static void generateAndPrintSingleSpec(String moduleName, long seed) {
        Generator generator = new Generator(seed);
        Spec spec = generator.generateSpec(moduleName);
        String tlaText = TLAPrinter.print(spec);
        System.out.println(tlaText);
    }

    public static void demonstrateValidation() {
        System.out.println("=== Validation Demo ===");

        Generator generator = new Generator(42);
        SanyValidator validator = new SanyValidator();

        Spec spec = generator.generateSpec("ValidationDemo");
        String tlaText = TLAPrinter.print(spec);

        System.out.println("Generated specification:");
        System.out.println(tlaText);
        System.out.println();

        SanyValidator.ValidationResult result = validator.validateTLAText(tlaText);

        System.out.println("Validation result:");
        System.out.println("  Valid: " + result.isValid());
        System.out.println("  Errors: " + result.getErrors().size());
        System.out.println("  Warnings: " + result.getWarnings().size());

        if (result.hasErrors()) {
            System.out.println("  Error details:");
            result.getErrors().forEach(error -> System.out.println("    - " + error));
        }

        if (result.hasWarnings()) {
            System.out.println("  Warning details:");
            result.getWarnings().forEach(warning -> System.out.println("    - " + warning));
        }
    }
}
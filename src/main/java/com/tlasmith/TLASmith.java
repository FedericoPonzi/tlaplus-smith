package com.tlasmith;

import com.tlasmith.ast.Spec;
import com.tlasmith.generator.Generator;
import com.tlasmith.printer.TLAPrinter;
import com.tlasmith.validation.SanyValidator;

/**
 * Main API for TLA+-Smith library.
 *
 * Simple facade for generating and validating random TLA+ specifications.
 */
public class TLASmith {

    /**
     * Generate a random TLA+ specification with default settings.
     *
     * @param moduleName the name for the TLA+ module
     * @return a random TLA+ specification
     */
    public static Spec generateSpec(String moduleName) {
        Generator generator = new Generator();
        return generator.generateSpec(moduleName);
    }

    /**
     * Generate a random TLA+ specification with a specific seed for reproducibility.
     *
     * @param moduleName the name for the TLA+ module
     * @param seed random seed for reproducible generation
     * @return a random TLA+ specification
     */
    public static Spec generateSpec(String moduleName, long seed) {
        Generator generator = new Generator(seed);
        return generator.generateSpec(moduleName);
    }

    /**
     * Generate a random TLA+ specification with custom configuration.
     *
     * @param moduleName the name for the TLA+ module
     * @param seed random seed for reproducible generation
     * @param config custom generator configuration
     * @return a random TLA+ specification
     */
    public static Spec generateSpec(String moduleName, long seed, Generator.GeneratorConfig config) {
        Generator generator = new Generator(new java.util.Random(seed), config);
        return generator.generateSpec(moduleName);
    }

    /**
     * Convert a TLA+ specification to text format.
     *
     * @param spec the specification to convert
     * @return TLA+ text representation
     */
    public static String toTLAString(Spec spec) {
        return TLAPrinter.print(spec);
    }

    /**
     * Validate a TLA+ specification using SANY parser.
     *
     * @param spec the specification to validate
     * @return validation result with errors/warnings
     */
    public static SanyValidator.ValidationResult validate(Spec spec) {
        SanyValidator validator = new SanyValidator();
        return validator.validate(spec);
    }

    /**
     * Validate TLA+ text using SANY parser.
     *
     * @param tlaText the TLA+ text to validate
     * @return validation result with errors/warnings
     */
    public static SanyValidator.ValidationResult validateText(String tlaText) {
        SanyValidator validator = new SanyValidator();
        return validator.validateTLAText(tlaText);
    }

    /**
     * Generate and validate a random TLA+ specification in one call.
     *
     * @param moduleName the name for the TLA+ module
     * @param seed random seed for reproducible generation
     * @return validation result for the generated specification
     */
    public static SanyValidator.ValidationResult generateAndValidate(String moduleName, long seed) {
        Spec spec = generateSpec(moduleName, seed);
        return validate(spec);
    }
}
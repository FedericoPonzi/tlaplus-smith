package com.tlasmith.validation;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import static org.junit.jupiter.api.Assertions.*;

class SanyValidatorTest {
    private SanyValidator validator;

    @BeforeEach
    void setUp() {
        validator = new SanyValidator();
    }

    @Test
    void testSanyIsAvailable() {
        assertTrue(validator.isAvailable());
        assertEquals("TLA2Tools 1.8.0-SNAPSHOT", validator.getSanyVersion());
    }

    @Test
    void testValidTLASpecification() {
        String validSpec =
            "---- MODULE TestModule ----\n" +
            "EXTENDS Integers\n" +
            "VARIABLES x\n" +
            "\n" +
            "Init == x = 0\n" +
            "Next == x' = x + 1\n" +
            "====\n";

        SanyValidator.ValidationResult result = validator.validateTLAText(validSpec);
        assertTrue(result.isValid(), "Valid TLA+ specification should pass SANY validation");
        assertFalse(result.hasErrors());
    }

    @Test
    void testInvalidTLASpecification() {
        String invalidSpec =
            "---- MODULE TestModule ----\n" +
            "EXTENDS Integers\n" +
            "VARIABLES x\n" +
            "\n" +
            "Init == x = 0\n" +
            "Next == x' = x + undefinedVariable\n" +
            "====\n";

        SanyValidator.ValidationResult result = validator.validateTLAText(invalidSpec);
        assertFalse(result.isValid(), "Invalid TLA+ specification should fail SANY validation");
        assertTrue(result.hasErrors());

        // Should contain semantic error about undefined variable
        assertTrue(result.getErrors().stream()
                .anyMatch(error -> error.toLowerCase().contains("semantic") ||
                                 error.toLowerCase().contains("undefined")));
    }

    @Test
    void testEmptySpecification() {
        SanyValidator.ValidationResult result = validator.validateTLAText("");
        assertFalse(result.isValid());
        assertTrue(result.hasErrors());
        assertTrue(result.getErrors().stream()
                .anyMatch(error -> error.contains("empty")));
    }

    @Test
    void testMalformedModule() {
        String malformedSpec = "This is not a valid TLA+ module";

        SanyValidator.ValidationResult result = validator.validateTLAText(malformedSpec);
        assertFalse(result.isValid());
        assertTrue(result.hasErrors());
        assertTrue(result.getErrors().stream()
                .anyMatch(error -> error.contains("module structure")));
    }
}
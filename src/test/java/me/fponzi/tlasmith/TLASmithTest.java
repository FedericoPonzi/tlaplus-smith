package me.fponzi.tlasmith;

import me.fponzi.tlasmith.ast.Spec;
import me.fponzi.tlasmith.generator.Generator;
import me.fponzi.tlasmith.validation.SanyValidator;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class TLASmithTest {

    @Test
    void testSimpleGeneration() {
        Spec spec = TLASmith.generateSpec("TestModule");
        assertNotNull(spec);
        assertEquals("TestModule", spec.getModuleName());
    }

    @Test
    void testGenerationWithSeed() {
        Spec spec1 = TLASmith.generateSpec("TestModule", 42);
        Spec spec2 = TLASmith.generateSpec("TestModule", 42);

        // Same seed should produce same structure
        assertEquals(spec1.getVariables().size(), spec2.getVariables().size());
        assertEquals(spec1.getConstants().size(), spec2.getConstants().size());
    }

    @Test
    void testToTLAString() {
        Spec spec = TLASmith.generateSpec("TestModule", 42);
        String tlaText = TLASmith.toTLAString(spec);

        assertNotNull(tlaText);
        assertTrue(tlaText.contains("---- MODULE TestModule ----"));
        assertTrue(tlaText.contains("===="));
    }

    @Test
    void testValidation() {
        Spec spec = TLASmith.generateSpec("TestModule", 42);
        SanyValidator.ValidationResult result = TLASmith.validate(spec);

        assertNotNull(result);
        // Generated specs MUST be valid
        assertTrue(result.isValid(), "Generated spec must be SANY-valid. Errors: " + result.getErrors());
    }

    @Test
    void testValidateText() {
        String validTLA =
            "---- MODULE Test ----\n" +
            "EXTENDS Integers\n" +
            "VARIABLES x\n" +
            "Init == x = 0\n" +
            "====\n";

        SanyValidator.ValidationResult result = TLASmith.validateText(validTLA);
        assertNotNull(result);
        assertTrue(result.isValid());
    }

    @Test
    void testGenerateAndValidate() {
        SanyValidator.ValidationResult result = TLASmith.generateAndValidate("TestModule", 42);
        assertNotNull(result);
        assertTrue(result.isValid(), "Generated spec must be SANY-valid. Errors: " + result.getErrors());
    }

    @Test
    void testCustomConfig() {
        Generator.GeneratorConfig config = new Generator.GeneratorConfig(
            2, 1, 2, 1, 2, 0.5, 0.3, 0.2, 0.0
        );

        Spec spec = TLASmith.generateSpec("TestModule", 42, config);
        assertNotNull(spec);
        assertEquals("TestModule", spec.getModuleName());
    }
}
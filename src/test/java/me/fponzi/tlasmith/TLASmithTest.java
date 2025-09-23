package me.fponzi.tlasmith;

import me.fponzi.tlasmith.ast.Spec;
import me.fponzi.tlasmith.generator.Generator;
import me.fponzi.tlasmith.validation.SanyValidator;
import org.junit.jupiter.api.Test;
import util.Assert;

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
        // Create config that GUARANTEES parameterized operators
        Generator.GeneratorConfig config = new Generator.GeneratorConfig(
            4, 2, 3, 1, 2, 0.3, 0.4, 0.2, 0.1,
            1, 2,  // minOperators=1, maxOperators=2 (at least 1 operator)
            2, 2   // minOperatorParameters=2, maxOperatorParameters=2 (operators MUST have 2 parameters)
        );

        Spec spec = TLASmith.generateSpec("TestModule", 12345, config);

        // Debug: Check what operators were actually generated
        System.out.println("Generated operators:");
        for (var op : spec.getOperators()) {
            System.out.println("  " + op.getName() + " with " + op.getParameters().size() + " parameters: " + op.getParameters());
            System.out.println("  Definition: " + op.toDefinitionString());
        }

        String tlaText = TLASmith.toTLAString(spec);
        System.out.println("Generated spec with forced parameterized operators:");
        System.out.println(tlaText);

        assertNotNull(tlaText);
        assertTrue(tlaText.contains("---- MODULE TestModule ----"));
        assertTrue(tlaText.contains("===="));

        // Should now contain operators with parameters like Op(a, b)
        assertTrue(tlaText.contains("Op("), "Should contain parameterized operator Op(a, b)");
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
            2, 1, 2, 1, 2, 0.5, 0.3, 0.2, 0.0,
            0, 2, 0, 2  // min/maxOperators, min/maxOperatorParameters
        );

        Spec spec = TLASmith.generateSpec("TestModule", 42, config);
        assertNotNull(spec);
        assertEquals("TestModule", spec.getModuleName());
    }
}
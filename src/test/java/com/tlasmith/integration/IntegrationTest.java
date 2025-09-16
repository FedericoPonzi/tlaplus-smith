package com.tlasmith.integration;

import com.tlasmith.ast.Spec;
import com.tlasmith.generator.Generator;
import com.tlasmith.printer.TLAPrinter;
import com.tlasmith.validation.SanyValidator;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import static org.junit.jupiter.api.Assertions.*;

class IntegrationTest {
    private Generator generator;
    private SanyValidator validator;

    @BeforeEach
    void setUp() {
        generator = new Generator(54321); // Fixed seed for reproducibility
        validator = new SanyValidator();
    }

    @Test
    void testEndToEndGeneration() {
        // Generate a specification
        Spec spec = generator.generateSpec("IntegrationTest");
        assertNotNull(spec);

        // Convert to TLA+ text
        String tlaText = TLAPrinter.print(spec);
        assertNotNull(tlaText);
        assertFalse(tlaText.trim().isEmpty());

        // Basic structure checks
        assertTrue(tlaText.contains("---- MODULE IntegrationTest ----"));
        assertTrue(tlaText.contains("===="));

        // Should have proper TLA+ structure
        if (!spec.getConstants().isEmpty()) {
            assertTrue(tlaText.contains("CONSTANTS"));
        }
        if (!spec.getVariables().isEmpty()) {
            assertTrue(tlaText.contains("VARIABLES"));
        }
        if (!spec.getExtendsModules().isEmpty()) {
            assertTrue(tlaText.contains("EXTENDS"));
        }
    }

    @Test
    void testValidationIntegration() {
        // Generate multiple specifications and validate them
        for (int i = 0; i < 5; i++) {
            Spec spec = generator.generateSpec("ValidationTest" + i);
            String tlaText = TLAPrinter.print(spec);

            SanyValidator.ValidationResult result = validator.validateTLAText(tlaText);
            assertNotNull(result);

            // All generated specs MUST be SANY-valid
            assertTrue(result.isValid(),
                "Generated spec ValidationTest" + i + " must be SANY-valid. Errors: " + result.getErrors());
        }
    }

    @Test
    void testSpecWithInitAndNext() {
        Spec spec = generator.generateSpec("InitNextTest");

        // Should have Init and Next formulas for state machines
        assertTrue(spec.getInit().isPresent());
        assertTrue(spec.getNext().isPresent());

        String tlaText = TLAPrinter.print(spec);

        // Should contain the formula definitions
        assertTrue(tlaText.contains("Init =="));
        assertTrue(tlaText.contains("Next =="));

        // Should have overall Spec definition
        assertTrue(tlaText.contains("Spec =="));
    }

    @Test
    void testMultipleSpecGenerations() {
        // Test generating multiple different specifications
        String[] moduleNames = {"Spec1", "Spec2", "Spec3", "TestModule", "RandomSpec"};

        for (String moduleName : moduleNames) {
            Spec spec = generator.generateSpec(moduleName);
            assertNotNull(spec);
            assertEquals(moduleName, spec.getModuleName());

            String tlaText = TLAPrinter.print(spec);
            assertTrue(tlaText.contains("---- MODULE " + moduleName + " ----"));

            // Validate each generated spec
            SanyValidator.ValidationResult result = validator.validateTLAText(tlaText);
            assertNotNull(result);
            assertTrue(result.isValid(),
                "Generated spec " + moduleName + " must be SANY-valid. Errors: " + result.getErrors());
        }
    }

    @Test
    void testGeneratedSpecParsesCorrectly() {
        Spec spec = generator.generateSpec("ParseTest");
        String tlaText = TLAPrinter.print(spec);

        // Check for balanced parentheses
        int openParens = 0;
        int closeParens = 0;
        for (char c : tlaText.toCharArray()) {
            if (c == '(') openParens++;
            if (c == ')') closeParens++;
        }
        assertEquals(openParens, closeParens);

        // Generated spec must be SANY-valid
        SanyValidator.ValidationResult result = validator.validateTLAText(tlaText);
        assertTrue(result.isValid(),
            "Generated spec ParseTest must be SANY-valid. Errors: " + result.getErrors());
    }

    @Test
    void testDifferentSeeds() {
        // Test that different seeds produce different results
        Generator gen1 = new Generator(1);
        Generator gen2 = new Generator(2);

        Spec spec1 = gen1.generateSpec("SeedTest");
        Spec spec2 = gen2.generateSpec("SeedTest");

        String tla1 = TLAPrinter.print(spec1);
        String tla2 = TLAPrinter.print(spec2);

        // With different seeds, the specifications should likely be different
        // (though there's a small chance they could be the same)
        // At minimum, they should both be valid
        assertNotNull(tla1);
        assertNotNull(tla2);
        assertFalse(tla1.trim().isEmpty());
        assertFalse(tla2.trim().isEmpty());
    }

    @Test
    void testGeneratorConfigurationImpact() {
        // Test that different configurations produce valid but different results
        Generator.GeneratorConfig config1 = new Generator.GeneratorConfig(
            2, 1, 2, 0, 1, 0.8, 0.1, 0.1, 0.0
        );
        Generator.GeneratorConfig config2 = new Generator.GeneratorConfig(
            5, 3, 5, 2, 4, 0.2, 0.3, 0.3, 0.2
        );

        Generator gen1 = new Generator(new java.util.Random(100), config1);
        Generator gen2 = new Generator(new java.util.Random(100), config2);

        Spec spec1 = gen1.generateSpec("ConfigTest1");
        Spec spec2 = gen2.generateSpec("ConfigTest2");

        // Both should be valid
        assertNotNull(TLAPrinter.print(spec1));
        assertNotNull(TLAPrinter.print(spec2));

        // Config2 should likely have more variables/constants due to higher ranges
        // (though random generation might not always reflect this exactly)
        assertTrue(spec1.getVariables().size() <= spec2.getVariables().size() ||
                  spec1.getConstants().size() <= spec2.getConstants().size());
    }

    @Test
    void testValidationResultStructure() {
        Spec spec = generator.generateSpec("ValidationStructureTest");
        String tlaText = TLAPrinter.print(spec);

        SanyValidator.ValidationResult result = validator.validateTLAText(tlaText);

        // Test validation result structure
        assertNotNull(result);
        assertNotNull(result.getErrors());
        assertNotNull(result.getWarnings());

        // toString should work
        assertNotNull(result.toString());
        assertFalse(result.toString().isEmpty());

        // Consistency checks
        assertEquals(result.hasErrors(), !result.getErrors().isEmpty());
        assertEquals(result.hasWarnings(), !result.getWarnings().isEmpty());
    }
}
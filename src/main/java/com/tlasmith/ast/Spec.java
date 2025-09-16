package com.tlasmith.ast;

import java.util.*;
import java.util.stream.Collectors;

public class Spec {
    private final String moduleName;
    private final List<String> extendsModules;
    private final List<String> constants;
    private final List<String> variables;
    private final List<Formula> formulas;

    public Spec(String moduleName, List<String> extendsModules,
                List<String> constants, List<String> variables, List<Formula> formulas) {
        this.moduleName = Objects.requireNonNull(moduleName, "Module name cannot be null");
        this.extendsModules = new ArrayList<>(Objects.requireNonNull(extendsModules));
        this.constants = new ArrayList<>(Objects.requireNonNull(constants));
        this.variables = new ArrayList<>(Objects.requireNonNull(variables));
        this.formulas = new ArrayList<>(Objects.requireNonNull(formulas));
    }

    public String getModuleName() {
        return moduleName;
    }

    public List<String> getExtendsModules() {
        return Collections.unmodifiableList(extendsModules);
    }

    public List<String> getConstants() {
        return Collections.unmodifiableList(constants);
    }

    public List<String> getVariables() {
        return Collections.unmodifiableList(variables);
    }

    public List<Formula> getFormulas() {
        return Collections.unmodifiableList(formulas);
    }

    public Optional<Formula> getInit() {
        return formulas.stream()
                .filter(f -> f.getType() == Formula.FormulaType.INIT)
                .findFirst();
    }

    public Optional<Formula> getNext() {
        return formulas.stream()
                .filter(f -> f.getType() == Formula.FormulaType.NEXT)
                .findFirst();
    }

    public List<Formula> getInvariants() {
        return formulas.stream()
                .filter(f -> f.getType() == Formula.FormulaType.INVARIANT)
                .collect(Collectors.toList());
    }

    public String toTLAString() {
        StringBuilder sb = new StringBuilder();

        // Module header
        String header = String.format("---- MODULE %s ----", moduleName);
        sb.append(header).append("\n");

        // EXTENDS
        if (!extendsModules.isEmpty()) {
            sb.append("EXTENDS ").append(String.join(", ", extendsModules)).append("\n");
        }

        // CONSTANTS
        if (!constants.isEmpty()) {
            sb.append("CONSTANTS ").append(String.join(", ", constants)).append("\n");
        }

        // VARIABLES
        if (!variables.isEmpty()) {
            sb.append("VARIABLES ").append(String.join(", ", variables)).append("\n");
        }

        sb.append("\n");

        // Formula definitions
        for (Formula formula : formulas) {
            sb.append(formula.toDefinitionString()).append("\n\n");
        }

        // Specification formula (if Init and Next exist)
        Optional<Formula> init = getInit();
        Optional<Formula> next = getNext();
        if (init.isPresent() && next.isPresent()) {
            String varsStr = variables.isEmpty() ? "" : "<<" + String.join(", ", variables) + ">>";
            sb.append("Spec == ").append(init.get().getName())
              .append(" /\\ [][").append(next.get().getName()).append("]_").append(varsStr)
              .append("\n\n");
        }

        // Module footer
        sb.append("====");

        return sb.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Spec spec = (Spec) obj;
        return Objects.equals(moduleName, spec.moduleName) &&
               Objects.equals(extendsModules, spec.extendsModules) &&
               Objects.equals(constants, spec.constants) &&
               Objects.equals(variables, spec.variables) &&
               Objects.equals(formulas, spec.formulas);
    }

    @Override
    public int hashCode() {
        return Objects.hash(moduleName, extendsModules, constants, variables, formulas);
    }

    @Override
    public String toString() {
        return "Spec{" + moduleName + ", vars=" + variables.size() +
               ", formulas=" + formulas.size() + "}";
    }

    public static class Builder {
        private String moduleName;
        private final List<String> extendsModules = new ArrayList<>();
        private final List<String> constants = new ArrayList<>();
        private final List<String> variables = new ArrayList<>();
        private final List<Formula> formulas = new ArrayList<>();

        public Builder moduleName(String moduleName) {
            this.moduleName = moduleName;
            return this;
        }

        public Builder extend(String module) {
            this.extendsModules.add(module);
            return this;
        }

        public Builder constant(String constant) {
            this.constants.add(constant);
            return this;
        }

        public Builder constants(List<String> constants) {
            this.constants.addAll(constants);
            return this;
        }

        public Builder variable(String variable) {
            this.variables.add(variable);
            return this;
        }

        public Builder variables(List<String> variables) {
            this.variables.addAll(variables);
            return this;
        }

        public Builder formula(Formula formula) {
            this.formulas.add(formula);
            return this;
        }

        public Spec build() {
            return new Spec(moduleName, extendsModules, constants, variables, formulas);
        }
    }
}
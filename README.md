# TLA+-Smith

A random TLA+ specification generator inspired by Csmith for C. TLA+-Smith generates syntactically and semantically valid TLA+ specifications for testing formatters, parsers, and other TLA+ tools.

## Features

- **AST-first approach**: Represents TLA+ constructs using type-safe Java classes
- **Semantic validity**: Tracks variables and constants to ensure generated expressions are semantically correct
- **Environment tracking**: Maintains scope of declared identifiers to prevent undefined variable references
- **Configurable generation**: Adjustable depth limits, variable counts, and operator probabilities
- **Pretty printing**: Converts AST back to readable TLA+ text
- **Extensible design**: Easy to add support for quantifiers, LETs, temporal operators, and more
- **SANY integration stub**: Framework ready for integration with TLA+ SANY parser

## Supported TLA+ Constructs

### Current Support
- **Variables and Constants**: `VARIABLES x, y` and `CONSTANTS N, MaxVal`
- **Literals**: Boolean (`TRUE`, `FALSE`), integer (`0`, `42`), and string (`"hello"`)
- **Binary Operators**:
  - Arithmetic: `+`, `-`, `*`
  - Logical: `/\` (and), `\/` (or), `=>` (implies)
  - Comparison: `=`, `#`, `<`, `>`, `<=`, `>=`
  - Set relations: `\in`, `\subseteq`, `\subset`
- **Formulas**: `Init` (initial state) and `Next` (next-state relation)
- **Complete Specifications**: Full TLA+ modules with proper structure

### Future Extensions (Placeholders Ready)
- Quantifiers (`\A`, `\E`)
- LET expressions
- Temporal operators (`[]`, `<>`, `~>`)
- Sequence and function operators
- Set comprehensions

## Installation and Setup

### Prerequisites
- Java 11 or higher
- Gradle (wrapper included)

### Building the Project

```bash
# Clone or extract the project
cd tlaplus-smith

# Build the project
./gradlew build

# Run tests
./gradlew test

# Create executable JAR
./gradlew jar
```

## Usage

### Running the Generator

#### Basic Usage
```bash
# Generate 3 random specifications (default)
./gradlew run

# Generate 5 specifications
./gradlew run --args="5"

# Generate 2 specifications with specific seed for reproducibility
./gradlew run --args="2 12345"
```

#### Running the JAR directly
```bash
# Build the JAR first
./gradlew jar

# Run with java
java -jar build/libs/tlaplus-smith-1.0.0.jar [num_specs] [seed]
```

### Example Output

```tla
---- MODULE RandomSpec1 ----
EXTENDS Integers
CONSTANTS C, C2
VARIABLES x, x2, x3

Init == (x = 0 /\ x2 > C) /\ x3 = TRUE

Next == (x < C2 /\ x' = x + 1 /\ x2' = x2 /\ x3' = FALSE) \/
        (x3 = TRUE /\ x' = x /\ x2' = x2 - 1 /\ x3' = x3)

Spec == Init /\ [][Next]_<<x, x2, x3>>
====
```

### Programmatic Usage

```java
import com.tlasmith.generator.Generator;
import com.tlasmith.ast.Spec;
import com.tlasmith.printer.TLAPrinter;

// Create generator with specific seed
Generator generator = new Generator(12345);

// Generate a specification
Spec spec = generator.generateSpec("MyModule");

// Convert to TLA+ text
String tlaText = TLAPrinter.print(spec);
System.out.println(tlaText);

// Validate (basic validation)
SanyValidator validator = new SanyValidator();
ValidationResult result = validator.validateTLAText(tlaText);
if (result.isValid()) {
    System.out.println("Generated valid TLA+ specification!");
}
```

### Custom Configuration

```java
// Create custom configuration
Generator.GeneratorConfig config = new Generator.GeneratorConfig(
    5,     // maxDepth
    2, 4,  // min/max variables
    1, 2,  // min/max constants
    0.4,   // literal probability
    0.3,   // variable probability
    0.2,   // constant probability
    0.1    // binary operation probability
);

Generator generator = new Generator(new Random(seed), config);
```

## Architecture

### AST Design
The project uses a visitor pattern for AST nodes with the base `Expr` interface. All TLA+ constructs are represented as type-safe Java objects that can be traversed and manipulated programmatically.

### Generation Process
1. **Environment Setup**: Create tracking for variables and constants
2. **Recursive Generation**: Generate expressions respecting depth limits and semantic constraints
3. **Pretty Printing**: Convert AST to syntactically correct TLA+ text
4. **Validation**: Check generated specifications for basic correctness

### Semantic Constraints
- Only reference declared variables and constants
- Respect operator arity requirements
- Generate type-consistent expressions
- Ensure proper formula structure (Init/Next patterns)

## Testing

```bash
# Run all tests
./gradlew test

# Run specific test class
./gradlew test --tests "com.tlasmith.ast.ExprTest"

# Run tests with verbose output
./gradlew test --info
```

### Test Categories
- **Unit Tests**: Individual AST nodes, generator components
- **Integration Tests**: End-to-end generation and validation
- **Property Tests**: Semantic correctness validation

## Development

### Adding New Operators
1. Add operator to `BinaryOp.Operator` enum
2. Update operator selection logic in `Generator`
3. Add pretty-printing support in `TLAPrinter`
4. Write tests for the new operator

### Adding New AST Nodes
1. Implement the `Expr` interface
2. Add visitor method to `ExprVisitor`
3. Update `TLAStringVisitor` for pretty-printing
4. Add generation logic to `Generator`
5. Write comprehensive tests

### SANY Integration
The `SanyValidator` class provides a framework for integrating with TLA+ SANY parser:

1. Implement `validateWithFullSany()` method
2. Add file I/O for temporary TLA+ files
3. Execute SANY via command line or Java API
4. Parse SANY output into `ValidationResult`

## Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass: `./gradlew test`
5. Submit a pull request

## Future Work

- **Quantifiers**: `\A` and `\E` with proper bound variable handling
- **LET expressions**: Local definitions within expressions
- **Temporal operators**: `[]`, `<>`, `~>` for temporal logic
- **Advanced types**: Sequences, functions, records
- **Mutation operators**: For differential testing
- **SANY integration**: Full parser integration for validation
- **Performance optimization**: Faster generation for large specifications
- **Configuration DSL**: More expressive generation controls

## License

[Specify license here]

## Acknowledgments

Inspired by Csmith for C and designed to support the TLA+ ecosystem with robust random testing capabilities.
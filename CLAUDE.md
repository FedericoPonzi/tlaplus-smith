# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

TLA+-Smith is a random TLA+ specification generator inspired by Csmith for C. It generates syntactically and semantically valid TLA+ specifications for testing TLA+ tools like formatters, parsers, and validators.

## Build System & Commands

This project uses Gradle with Java 21 toolchain but targets Java 11 compatibility.

### Essential Commands
```bash
# Build the project
./gradlew build

# Run tests
./gradlew test

# Run specific test class
./gradlew test --tests "me.fponzi.tlasmith.ast.ExprTest"

# Run the application (generates 3 random specs by default)
./gradlew run

# Run with arguments (number of specs and optional seed)
./gradlew run --args="5"
./gradlew run --args="2 12345"

# Create executable JAR with all dependencies
./gradlew fatJar

# Clean build directory
./gradlew clean
```

### Testing
- Uses JUnit 5 platform
- Test categories: Unit tests (AST nodes, components), Integration tests (end-to-end), Property tests (semantic validation)
- All tests must pass before considering any feature complete

## Architecture

### Core Components
- **AST Package** (`me.fponzi.tlasmith.ast`): Type-safe representation of TLA+ constructs using visitor pattern
  - `Expr` interface: Base for all expressions
  - `ExprVisitor<T>`: Visitor pattern for AST traversal
  - Concrete types: `Var`, `Const`, `Literal`, `BinaryOp`, `Formula`, `Spec`

- **Generator** (`me.fponzi.tlasmith.generator.Generator`): Core random generation logic
  - Configurable via `GeneratorConfig` (depth limits, variable counts, operator probabilities)
  - Uses `Environment` for semantic constraint tracking

- **Printer** (`me.fponzi.tlasmith.printer.TLAPrinter`): Converts AST to readable TLA+ text

- **Validation** (`me.fponzi.tlasmith.validation`): SANY parser integration for validation
  - `SanyValidator`: Main validation interface
  - Exception hierarchy: `SanyException` with subtypes for different error types

- **Main API** (`me.fponzi.tlasmith.TLASmith`): Simple facade for library usage

### Key Design Principles
- AST-first approach with type safety
- Environment tracking for semantic validity (prevents undefined variable references)
- All binary operations wrapped in parentheses to eliminate precedence conflicts
- Visitor pattern for extensible AST processing

### Dependencies
- `org.lamport:tla2tools:1.8.0-SNAPSHOT` - TLA+ SANY parser integration
- `commons-io:commons-io:2.16.1` - File I/O utilities
- JUnit 5 for testing

## Development Workflow

### Adding New TLA+ Operators
1. Add to `BinaryOp.Operator` enum with symbol and precedence info
2. Update operator selection logic in `Generator`
3. Add pretty-printing support in `TLAPrinter`
4. Write comprehensive tests

### Adding New AST Nodes
1. Implement `Expr` interface with visitor support
2. Add visitor method to `ExprVisitor<T>`
3. Update `TLAStringVisitor` for text conversion
4. Add generation logic to `Generator`
5. Write unit and integration tests

### Code Quality
- Follow existing Java conventions and patterns
- Maintain semantic validity constraints
- Use TDD approach with failing tests first
- Ensure all expressions remain semantically correct (no undefined variables)
- Test both individual components and end-to-end generation
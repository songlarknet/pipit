# Next steps

What should I implement next?

## Compilation and backend improvements
### Better codegen
Mifta's thesis fixes the duplication of work, but probably requires a bit more work to remove intermediate values

### Common subexpression elimination
Useful for proofs and code generation - very useful

### FFI / separate compilation
* Useful for scaling but not necessarily interesting
* But if we can interop with array programs might be nice

### Explicit ObC language?
Interesting, useful for loops, goes well with separate compilation

## Source language improvements

### Source language plugin
* Nice for user programs
* Might be able to write nice refinements in programs

### Clocks
* Key missing feature
* Could do a simplified version like Kind2 implements

### Explicit refinements
* Support refinements as first class types

### Arrays
* Cool fusion
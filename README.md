# Valm Decompiler

A headless executor-side Luau bytecode reader, disassembler, and source reconstructor. It does not create a separate window and does not call an external decompiler API.

## Native reconstruction

- Reads Luau bytecode versions 3 through 14.
- Normalizes Roblox production opcode bytes before decoding while preserving standard unencoded Luau bytecode.
- Reconstructs common branches, if/else blocks, while loops, repeat loops, numeric for loops, and generic for loops.
- Reconstructs nested closures and consumes capture records after both NEWCLOSURE and DUPCLOSURE.
- Reconstructs captured locals and upvalues, varargs, and common table construction.
- Decodes one-, two-, and three-part GETIMPORT paths in Luau order.
- Accepts an explicit executor bytecode provider through `ValmDecompiler.SetBytecodeProvider`.
- Tracks register values and scopes across reconstructed blocks.
- Infers readable local names from debug-local lifetimes, Roblox services, child lookups, indexed properties, common method results, and protected-call results.
- Recognizes generic compiler-generated debug names such as LocalN, Pcall, and Xpcall so they do not override stronger semantic names.
- Removes redundant self-assignments without dropping initializers that may read an outer-scope value.
- Uses PascalCase output names by default.
- Exposes parsing, inspection, disassembly, synchronous decompilation, asynchronous decompilation, and cache controls.

## Valm Dex ++

Valm Dex ++ can load this module as its primary decompiler and pass the selected script's bytecode directly to it. The native reconstructor runs first; Bytefall remains an optional fallback when native reconstruction cannot recover source.

The public global API is `ValmDecompiler`, with `ValmDecompilerInstalledDecompile` as the installed decompile bridge.

## Limits

The native reconstructor is heuristic rather than a complete Luau compiler decompiler. Heavily flattened or virtualized state machines, irreducible control-flow graphs, and experimental class opcodes may still require a fallback. Reconstructed source should be checked before treating it as an exact recovery of the original script. The executor must expose bytecode for the selected script.

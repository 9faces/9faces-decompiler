# 9faces Decompiler

A headless executor-side Luau bytecode reader, disassembler, and source reconstructor. It does not create a separate window and does not call an external decompiler API.

## Native reconstruction

- Reads Luau bytecode versions 3 through 14.
- Correctly consumes auxiliary words for all six register-comparison jump instructions, preventing the instruction stream from becoming misaligned.
- Reconstructs common branches, if/else blocks, while loops, repeat loops, numeric for loops, and generic for loops.
- Reconstructs nested closures, captured upvalues, varargs, and table construction.
- Decodes one-, two-, and three-part GETIMPORT paths in Luau order.
- Accepts an explicit executor bytecode provider through `Ninefaces.SetBytecodeProvider`.
- Tracks register values and scopes across reconstructed blocks.
- Folds safe constant arithmetic and selected deterministic string, math, and bit32 calls.
- Supports PascalCase output names by default.
- Includes the 9faces ASCII banner at the beginning of `Loader.lua`.

## Valm Dex ++

Valm Dex ++ loads this module as its primary decompiler and passes the selected script's bytecode directly to 9faces. Bytefall remains the first fallback only when native reconstruction returns no source.

## Limits

The native reconstructor is heuristic rather than a complete Luau compiler decompiler. Heavily flattened or virtualized state machines, irreducible control-flow graphs, and experimental class opcodes may still require a fallback. The executor must expose bytecode for the selected script.

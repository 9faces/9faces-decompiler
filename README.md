# 9faces Decompiler

A headless executor-side Luau bytecode reader, disassembler, and source reconstructor. It does not create a separate window and does not call an external decompiler API.

## Native reconstruction

- Reads Luau bytecode versions 3 through 14.
- Normalizes Roblox production opcode bytes before decoding while preserving standard unencoded Luau bytecode.
- Reconstructs common branches, if/else blocks, while loops, repeat loops, numeric for loops, and generic for loops.
- Reconstructs nested closures and consumes capture records after both NEWCLOSURE and DUPCLOSURE.
- Reconstructs captured locals and upvalues, varargs, and common table construction.
- Decodes one-, two-, and three-part GETIMPORT paths in Luau order.
- Accepts an explicit executor bytecode provider through `Ninefaces.SetBytecodeProvider`.
- Tracks register values and scopes across reconstructed blocks.
- Supports PascalCase output names by default.

## Valm Dex ++

Valm Dex ++ loads this module as its primary decompiler and passes the selected script's bytecode directly to 9faces. Bytefall remains the first fallback when native reconstruction returns no source. Valm Dex adds the 9faces banner to successfully decompiled output, not to the loader source or the decompiler UI.

## Limits

The native reconstructor is heuristic rather than a complete Luau compiler decompiler. Heavily flattened or virtualized state machines, irreducible control-flow graphs, and experimental class opcodes may still require a fallback. The executor must expose bytecode for the selected script.

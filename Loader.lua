-- VALM

local Env = (type(getgenv) == "function" and getgenv()) or _G
local GetScriptBytecode = Env.getscriptbytecode or Env.dumpstring or getscriptbytecode or dumpstring
local ActiveBytecodeProvider = GetScriptBytecode
local Cache = setmetatable({}, {__mode = "k"})
local CacheOrder = {}
local CacheLimit = 24
local MaxBytecodeBytes = 4194304
local MaxPrototypes = 2048
local MaxStrings = 32768
local MaxInstructions = 100000
local MaxOutputLines = 12000
local BytecodeVersionMin = 3
local BytecodeVersionMax = 14
local YieldCounter = 0
local YieldInterval = 512
local function YieldControl()
    YieldCounter = YieldCounter + 1
    if YieldCounter >= YieldInterval then
        YieldCounter = 0
        if type(task) == "table" and type(task.wait) == "function" then
            pcall(task.wait)
        end
    end
end
local OpcodeNames = {
    "NOP", "BREAK", "LOADNIL", "LOADB", "LOADN", "LOADK", "MOVE", "GETGLOBAL", "SETGLOBAL", "GETUPVAL", "SETUPVAL", "CLOSEUPVALS", "GETIMPORT", "GETTABLE", "SETTABLE", "GETTABLEKS", "SETTABLEKS", "GETTABLEN", "SETTABLEN", "NEWCLOSURE", "NAMECALL", "CALL", "RETURN", "JUMP", "JUMPBACK", "JUMPIF", "JUMPIFNOT", "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT", "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "ADDK", "SUBK", "MULK", "DIVK", "MODK", "POWK", "AND", "OR", "ANDK", "ORK", "CONCAT", "NOT", "MINUS", "LENGTH", "NEWTABLE", "DUPTABLE", "SETLIST", "FORNPREP", "FORNLOOP", "FORGLOOP", "FORGPREP_INEXT", "FASTCALL3", "FORGPREP_NEXT", "NATIVECALL", "GETVARARGS", "DUPCLOSURE", "PREPVARARGS", "LOADKX", "JUMPX", "FASTCALL", "COVERAGE", "CAPTURE", "SUBRK", "DIVRK", "FASTCALL1", "FASTCALL2", "FASTCALL2K", "FORGPREP", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "IDIV", "IDIVK", "GETUDATAKS", "SETUDATAKS", "NAMECALLUDATA", "NEWCLASSMEMBER", "CALLFB", "CMPPROTO", "FASTPCALL", "NEWCLASS", "CONSTRUCT", "FINCONSTRUCT", "GETPRIVATEFIELD", "SETPRIVATEFIELD"
}
local OpcodeLookup = {}
for Index, Name in ipairs(OpcodeNames) do
    OpcodeLookup[Name] = Index - 1
end
local AuxiliaryOpcodes = {}
for _, Name in ipairs({"GETGLOBAL", "SETGLOBAL", "GETIMPORT", "GETTABLEKS", "SETTABLEKS", "NAMECALL", "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT", "NEWTABLE", "SETLIST", "FORGLOOP", "FASTCALL3", "LOADKX", "FASTCALL2", "FASTCALL2K", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "GETUDATAKS", "SETUDATAKS", "NAMECALLUDATA", "NEWCLASSMEMBER", "CALLFB", "CMPPROTO", "NEWCLASS", "CONSTRUCT", "GETPRIVATEFIELD", "SETPRIVATEFIELD"}) do
    AuxiliaryOpcodes[OpcodeLookup[Name]] = true
end
local ControlFlowOpcodes = {}
for _, Name in ipairs({"JUMP", "JUMPBACK", "JUMPIF", "JUMPIFNOT", "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT", "FORNPREP", "FORNLOOP", "FORGLOOP", "FORGPREP_INEXT", "FORGPREP_NEXT", "JUMPX", "FORGPREP", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "CMPPROTO"}) do
    ControlFlowOpcodes[OpcodeLookup[Name]] = true
end
local Keywords = {
    ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true, ["elseif"] = true, ["end"] = true,
    ["false"] = true, ["for"] = true, ["function"] = true, ["if"] = true, ["in"] = true, ["local"] = true,
    ["nil"] = true, ["not"] = true, ["or"] = true, ["repeat"] = true, ["return"] = true, ["then"] = true,
    ["true"] = true, ["until"] = true, ["while"] = true, ["continue"] = true, ["type"] = true, ["export"] = true
}
local function PascalCase(Value)
    local Text = tostring(Value or "")
    Text = Text:gsub("([%l%d])([A-Z])", "%1 %2")
    Text = Text:gsub("[^%w]", " ")
    local Parts = {}
    for Part in Text:gmatch("[%a%d]+") do
        if Part ~= "" then
            local Lower = Part:lower()
            Parts[#Parts + 1] = Lower:sub(1, 1):upper() .. Lower:sub(2)
        end
    end
    local Result = table.concat(Parts)
    if Result == "" or Result:match("^%d") then
        Result = "Local" .. Result
    end
    if Keywords[Result:lower()] then
        Result = "Local" .. Result
    end
    return Result
end
local function IsIdentifier(Value)
    return type(Value) == "string" and Value:match("^[%a_][%w_]*$") ~= nil and not Keywords[Value]
end
local function Quote(Value)
    return string.format("%q", tostring(Value))
end
local function NewReader(Data)
    return {Data = Data, Offset = 0, Length = #Data}
end
local function Ensure(Reader, Count)
    if Count < 0 or Reader.Offset + Count > Reader.Length then
        error("Unexpected end of bytecode at offset " .. tostring(Reader.Offset), 0)
    end
end
local function ReadByte(Reader)
    Ensure(Reader, 1)
    local Value = string.byte(Reader.Data, Reader.Offset + 1)
    Reader.Offset = Reader.Offset + 1
    return Value
end
local function ReadBytes(Reader, Count)
    Ensure(Reader, Count)
    local First = Reader.Offset + 1
    local Last = Reader.Offset + Count
    Reader.Offset = Reader.Offset + Count
    return Reader.Data:sub(First, Last)
end
local function ReadU32(Reader)
    Ensure(Reader, 4)
    local A, B, C, D = string.byte(Reader.Data, Reader.Offset + 1, Reader.Offset + 4)
    Reader.Offset = Reader.Offset + 4
    return A + B * 256 + C * 65536 + D * 16777216
end
local function ReadI32(Reader)
    local Value = ReadU32(Reader)
    if Value >= 2147483648 then
        return Value - 4294967296
    end
    return Value
end
local function ReadVarInt(Reader)
    local Result = 0
    local Multiplier = 1
    for _ = 1, 5 do
        local Byte = ReadByte(Reader)
        Result = Result + (Byte % 128) * Multiplier
        if Byte < 128 then
            return Result
        end
        Multiplier = Multiplier * 128
    end
    error("Varint exceeds five bytes", 0)
end
local function ReadVarInt64String(Reader)
    local Chunks = {}
    local Finished = false
    for _ = 1, 10 do
        local Byte = ReadByte(Reader)
        Chunks[#Chunks + 1] = Byte % 128
        if Byte < 128 then
            Finished = true
            break
        end
    end
    if not Finished then
        error("64-bit varint exceeds ten bytes", 0)
    end
    local Digits = {0}
    for ChunkIndex = #Chunks, 1, -1 do
        local Carry = Chunks[ChunkIndex]
        for DigitIndex = 1, #Digits do
            local Value = Digits[DigitIndex] * 128 + Carry
            Digits[DigitIndex] = Value % 10
            Carry = math.floor(Value / 10)
        end
        while Carry > 0 do
            Digits[#Digits + 1] = Carry % 10
            Carry = math.floor(Carry / 10)
        end
    end
    local Characters = {}
    for DigitIndex = #Digits, 1, -1 do
        Characters[#Characters + 1] = tostring(Digits[DigitIndex])
    end
    return table.concat(Characters)
end
local function SkipVarInt64(Reader)
    ReadVarInt64String(Reader)
end
local function ReadDouble(Reader)
    local Low = ReadU32(Reader)
    local High = ReadU32(Reader)
    local Sign = High >= 2147483648 and -1 or 1
    local Exponent = math.floor((High % 2147483648) / 1048576)
    local Fraction = (High % 1048576) * 4294967296 + Low
    if Exponent == 2047 then
        if Fraction == 0 then
            return Sign * math.huge
        end
        return 0 / 0
    end
    if Exponent == 0 then
        if Fraction == 0 then
            return Sign * 0
        end
        return Sign * Fraction * (2 ^ -1074)
    end
    return Sign * (1 + Fraction / 4503599627370496) * (2 ^ (Exponent - 1023))
end
local function ReadFloat(Reader)
    local Value = ReadU32(Reader)
    local Sign = Value >= 2147483648 and -1 or 1
    local Exponent = math.floor((Value % 2147483648) / 8388608)
    local Fraction = Value % 8388608
    if Exponent == 255 then
        if Fraction == 0 then
            return Sign * math.huge
        end
        return 0 / 0
    end
    if Exponent == 0 then
        if Fraction == 0 then
            return Sign * 0
        end
        return Sign * Fraction * (2 ^ -149)
    end
    return Sign * (1 + Fraction / 8388608) * (2 ^ (Exponent - 127))
end
local function ReadStringRef(Reader, Strings)
    local Id = ReadVarInt(Reader)
    if Id == 0 then
        return nil
    end
    local Value = Strings[Id]
    if Value == nil then
        error("String table index is invalid: " .. tostring(Id), 0)
    end
    return Value
end
local function ReadConstant(Reader, Strings)
    local Tag = ReadByte(Reader)
    if Tag == 0 then
        return {Kind = "Nil", Value = nil}
    elseif Tag == 1 then
        return {Kind = "Boolean", Value = ReadByte(Reader) ~= 0}
    elseif Tag == 2 then
        return {Kind = "Number", Value = ReadDouble(Reader)}
    elseif Tag == 3 then
        return {Kind = "String", Value = ReadStringRef(Reader, Strings)}
    elseif Tag == 4 then
        return {Kind = "Import", Value = ReadU32(Reader)}
    elseif Tag == 5 then
        local Count = ReadVarInt(Reader)
        if Count > 65536 then
            error("Table constant exceeds the safety limit", 0)
        end
        local Keys = {}
        for Index = 1, Count do
            Keys[Index] = ReadVarInt(Reader)
            YieldControl()
        end
        return {Kind = "Table", Keys = Keys}
    elseif Tag == 6 then
        return {Kind = "Closure", Value = ReadVarInt(Reader)}
    elseif Tag == 7 then
        return {Kind = "Vector", Value = {ReadFloat(Reader), ReadFloat(Reader), ReadFloat(Reader), ReadFloat(Reader)}}
    elseif Tag == 8 then
        local Count = ReadVarInt(Reader)
        if Count > 65536 then
            error("Table constant exceeds the safety limit", 0)
        end
        local Entries = {}
        for Index = 1, Count do
            Entries[Index] = {Key = ReadVarInt(Reader), Value = ReadI32(Reader)}
            YieldControl()
        end
        return {Kind = "TableWithConstants", Entries = Entries}
    elseif Tag == 9 then
        local IsNegative = ReadByte(Reader) ~= 0
        local Magnitude = ReadVarInt64String(Reader)
        return {Kind = "Integer", Value = IsNegative and (Magnitude == "0" and "0" or "-" .. Magnitude) or Magnitude}
    elseif Tag == 10 then
        local ClassNameId = ReadVarInt(Reader)
        local PrivateFields = ReadByte(Reader)
        local PrivateMethods = ReadByte(Reader)
        local Properties = ReadVarInt(Reader)
        local Methods = ReadVarInt(Reader)
        local Members = {}
        for Index = 1, math.max(0, Properties - PrivateFields) do
            Members[#Members + 1] = ReadVarInt(Reader)
        end
        for Index = Properties + 1, Properties + Methods - PrivateMethods do
            Members[#Members + 1] = ReadVarInt(Reader)
        end
        return {Kind = "ClassShape", ClassNameId = ClassNameId, Members = Members, PrivateFields = PrivateFields, PrivateMethods = PrivateMethods}
    elseif Tag == 11 then
        return {Kind = "VectorD", Value = {ReadDouble(Reader), ReadDouble(Reader), ReadDouble(Reader), ReadDouble(Reader)}}
    end
    error("Unsupported constant tag " .. tostring(Tag), 0)
end
local function ReadProto(Reader, Version, TypeVersion, Strings, ProtoIndex)
    local ProtoSize
    if Version >= 12 then
        ProtoSize = ReadVarInt(Reader)
    end
    local ProtoStart = Reader.Offset
    local Proto = {
        Index = ProtoIndex,
        MaxStackSize = ReadByte(Reader),
        NumParams = ReadByte(Reader),
        NumUpvalues = ReadByte(Reader),
        IsVararg = ReadByte(Reader) ~= 0,
        Flags = 0,
        TypeInfo = "",
        Words = {},
        Constants = {},
        Children = {},
        DebugLocals = {},
        DebugUpvalues = {},
        Feedback = {}
    }
    if Version >= 4 then
        Proto.Flags = ReadByte(Reader)
        local TypeSize = ReadVarInt(Reader)
        if TypeSize > 1048576 then
            error("Type information exceeds the safety limit", 0)
        end
        Proto.TypeInfo = ReadBytes(Reader, TypeSize)
    end
    local CodeSize = ReadVarInt(Reader)
    if CodeSize > MaxInstructions then
        error("Instruction count exceeds the safety limit", 0)
    end
    for Index = 1, CodeSize do
        Proto.Words[Index] = ReadU32(Reader)
        YieldControl()
    end
    local ConstantCount = ReadVarInt(Reader)
    if ConstantCount > 1048576 then
        error("Constant count exceeds the safety limit", 0)
    end
    for Index = 1, ConstantCount do
        Proto.Constants[Index] = ReadConstant(Reader, Strings)
        YieldControl()
    end
    local ChildCount = ReadVarInt(Reader)
    if ChildCount > MaxPrototypes then
        error("Child prototype count exceeds the safety limit", 0)
    end
    for Index = 1, ChildCount do
        Proto.Children[Index] = ReadVarInt(Reader)
    end
    Proto.LineDefined = ReadVarInt(Reader)
    Proto.DebugName = ReadStringRef(Reader, Strings)
    local HasLineInfo = ReadByte(Reader)
    if HasLineInfo ~= 0 then
        Proto.LineGapLog2 = ReadByte(Reader)
        local IntervalCount = math.floor((math.max(0, CodeSize - 1)) / (2 ^ Proto.LineGapLog2)) + (CodeSize > 0 and 1 or 0)
        for Index = 1, CodeSize do
            ReadByte(Reader)
        end
        for Index = 1, IntervalCount do
            ReadI32(Reader)
        end
    end
    local HasDebugInfo = ReadByte(Reader)
    if HasDebugInfo ~= 0 then
        local LocalCount = ReadVarInt(Reader)
        if LocalCount > 262144 then
            error("Debug local count exceeds the safety limit", 0)
        end
        for Index = 1, LocalCount do
            Proto.DebugLocals[Index] = {
                Name = ReadStringRef(Reader, Strings),
                StartPC = ReadVarInt(Reader),
                EndPC = ReadVarInt(Reader),
                Register = ReadByte(Reader)
            }
        end
        local UpvalueCount = ReadVarInt(Reader)
        if UpvalueCount > 200 then
            error("Debug upvalue count exceeds the safety limit", 0)
        end
        for Index = 1, UpvalueCount do
            Proto.DebugUpvalues[Index] = ReadStringRef(Reader, Strings)
        end
    end
    if Version >= 11 then
        local FeedbackCount = ReadVarInt(Reader)
        if FeedbackCount > MaxInstructions then
            error("Feedback vector exceeds the safety limit", 0)
        end
        for Index = 1, FeedbackCount do
            local Kind = ReadByte(Reader)
            if Kind == 0 then
                Proto.Feedback[Index] = {Kind = "CallTarget", Value = ReadVarInt(Reader)}
            elseif Kind == 1 then
                Proto.Feedback[Index] = {Kind = "Construct", Value = ReadVarInt(Reader)}
            else
                error("Unknown feedback slot type " .. tostring(Kind), 0)
            end
        end
    end
    if Version >= 12 and math.floor(Proto.Flags / 8) % 2 == 1 then
        SkipVarInt64(Reader)
    end
    if ProtoSize then
        local EndOffset = ProtoStart + ProtoSize
        if EndOffset < Reader.Offset or EndOffset > Reader.Length then
            error("Prototype size is inconsistent with its contents", 0)
        end
        Reader.Offset = EndOffset
    end
    return Proto
end
local function DecodeInstructions(Proto)
    local Instructions = {}
    local PC = 1
    while PC <= #Proto.Words do
        YieldControl()
        local Word = Proto.Words[PC]
        local Opcode = Word % 256
        local Name = OpcodeNames[Opcode + 1]
        if not Name then
            error("Unknown opcode " .. tostring(Opcode) .. " at instruction " .. tostring(PC - 1), 0)
        end
        local A = math.floor(Word / 256) % 256
        local B = math.floor(Word / 65536) % 256
        local C = math.floor(Word / 16777216) % 256
        local D = math.floor((Word % 4294967296) / 65536)
        if D >= 32768 then
            D = D - 65536
        end
        local E = math.floor(Word / 256)
        if E >= 8388608 then
            E = E - 16777216
        end
        local Entry = {PC = PC - 1, Opcode = Opcode, Name = Name, A = A, B = B, C = C, D = D, E = E, Word = Word}
        if AuxiliaryOpcodes[Opcode] then
            if PC + 1 > #Proto.Words then
                error("Missing auxiliary word for " .. Name .. " at instruction " .. tostring(PC - 1), 0)
            end
            Entry.Aux = Proto.Words[PC + 1]
            PC = PC + 1
        end
        Instructions[#Instructions + 1] = Entry
        PC = PC + 1
    end
    Proto.Instructions = Instructions
    return Instructions
end
local RobloxOpcodeMultiplier = 203
local function IsOpcodeStreamValid(Protos, Multiplier)
    for _, Proto in ipairs(Protos) do
        local PC = 1
        while PC <= #Proto.Words do
            local Word = Proto.Words[PC]
            local EncodedOpcode = Word % 256
            local Opcode = (EncodedOpcode * Multiplier) % 256
            if OpcodeNames[Opcode + 1] == nil then
                return false, "Unknown opcode " .. tostring(Opcode) .. " at instruction " .. tostring(PC - 1)
            end
            if AuxiliaryOpcodes[Opcode] then
                if PC + 1 > #Proto.Words then
                    return false, "Missing auxiliary word for " .. OpcodeNames[Opcode + 1] .. " at instruction " .. tostring(PC - 1)
                end
                PC = PC + 2
            else
                PC = PC + 1
            end
        end
    end
    return true
end
local function NormalizeOpcodeEncoding(Protos)
    local StandardValid, StandardError = IsOpcodeStreamValid(Protos, 1)
    if StandardValid then
        return 1
    end
    local RobloxValid, RobloxError = IsOpcodeStreamValid(Protos, RobloxOpcodeMultiplier)
    if not RobloxValid then
        error("Invalid Luau opcode stream. Standard decoding: " .. tostring(StandardError) .. "; Roblox decoding: " .. tostring(RobloxError), 0)
    end
    for _, Proto in ipairs(Protos) do
        local PC = 1
        while PC <= #Proto.Words do
            local Word = Proto.Words[PC]
            local EncodedOpcode = Word % 256
            local Opcode = (EncodedOpcode * RobloxOpcodeMultiplier) % 256
            Proto.Words[PC] = Word - EncodedOpcode + Opcode
            if AuxiliaryOpcodes[Opcode] then
                PC = PC + 2
            else
                PC = PC + 1
            end
            YieldControl()
        end
    end
    return RobloxOpcodeMultiplier
end
local function ParseBytecode(Data)
    if type(Data) ~= "string" then
        error("Bytecode must be a string", 0)
    end
    if #Data < 3 then
        error("Bytecode is empty or truncated", 0)
    end
    if #Data > MaxBytecodeBytes then
        error("Bytecode exceeds the 4 MiB safety limit", 0)
    end
    local Reader = NewReader(Data)
    local Version = ReadByte(Reader)
    if Version == 0 then
        error("Compiler error: " .. Data:sub(2), 0)
    end
    if Version < BytecodeVersionMin or Version > BytecodeVersionMax then
        error("Valm Decompiler supports bytecode versions " .. tostring(BytecodeVersionMin) .. " through " .. tostring(BytecodeVersionMax) .. "; received version " .. tostring(Version), 0)
    end
    local TypeVersion = 0
    if Version >= 4 then
        TypeVersion = ReadByte(Reader)
        if TypeVersion < 1 or TypeVersion > 3 then
            error("Unsupported bytecode type version " .. tostring(TypeVersion), 0)
        end
    end
    local StringCount = ReadVarInt(Reader)
    if StringCount > MaxStrings then
        error("String table exceeds the safety limit", 0)
    end
    local Strings = {}
    for Index = 1, StringCount do
        YieldControl()
        local Length = ReadVarInt(Reader)
        if Length > MaxBytecodeBytes then
            error("String entry exceeds the safety limit", 0)
        end
        Strings[Index] = ReadBytes(Reader, Length)
    end
    if TypeVersion == 3 then
        local RemapIndex = ReadByte(Reader)
        local RemapCount = 0
        while RemapIndex ~= 0 do
            ReadStringRef(Reader, Strings)
            RemapCount = RemapCount + 1
            if RemapCount > 255 then
                error("Userdata type remapping table is invalid", 0)
            end
            RemapIndex = ReadByte(Reader)
        end
    end
    local ProtoCount = ReadVarInt(Reader)
    if ProtoCount < 1 or ProtoCount > MaxPrototypes then
        error("Prototype count is outside the supported range", 0)
    end
    local Protos = {}
    local TotalInstructions = 0
    for Index = 1, ProtoCount do
        YieldControl()
        local Proto = ReadProto(Reader, Version, TypeVersion, Strings, Index - 1)
        TotalInstructions = TotalInstructions + #Proto.Words
        if TotalInstructions > MaxInstructions then
            error("Total instruction count exceeds the safety limit", 0)
        end
        Protos[Index] = Proto
    end
    local MainProtoIndex = ReadVarInt(Reader)
    local MainProto = Protos[MainProtoIndex + 1]
    if not MainProto then
        error("Main prototype index is invalid", 0)
    end
    local OpcodeMultiplier = NormalizeOpcodeEncoding(Protos)
    for _, Proto in ipairs(Protos) do
        DecodeInstructions(Proto)
    end
    return {Version = Version, TypeVersion = TypeVersion, Strings = Strings, Protos = Protos, MainProto = MainProto, MainProtoIndex = MainProtoIndex, TotalInstructions = TotalInstructions, OpcodeMultiplier = OpcodeMultiplier}
end
local function GetConstant(Proto, Index)
    local Constant = Proto.Constants[Index + 1]
    if not Constant then
        error("Constant index " .. tostring(Index) .. " is outside the prototype table", 0)
    end
    return Constant
end
local function ConstantExpression(Proto, Index, Strings)
    local Constant = GetConstant(Proto, Index)
    if Constant.Kind == "Nil" then
        return "nil"
    elseif Constant.Kind == "Boolean" then
        return Constant.Value and "true" or "false"
    elseif Constant.Kind == "Number" then
        return tostring(Constant.Value)
    elseif Constant.Kind == "Integer" then
        return tostring(Constant.Value)
    elseif Constant.Kind == "String" then
        return Quote(Constant.Value or "")
    elseif Constant.Kind == "Vector" or Constant.Kind == "VectorD" then
        local V = Constant.Value
        return "Vector3.new(" .. tostring(V[1]) .. ", " .. tostring(V[2]) .. ", " .. tostring(V[3]) .. ")"
    elseif Constant.Kind == "Table" then
        return "{}"
    elseif Constant.Kind == "TableWithConstants" then
        local Entries = {}
        for _, Entry in ipairs(Constant.Entries) do
            if Entry.Value >= 0 then
                local KeyExpression = ConstantExpression(Proto, Entry.Key, Strings)
                local ValueExpression = ConstantExpression(Proto, Entry.Value, Strings)
                if IsIdentifier(KeyExpression) then
                    Entries[#Entries + 1] = KeyExpression .. " = " .. ValueExpression
                else
                    Entries[#Entries + 1] = "[" .. KeyExpression .. "] = " .. ValueExpression
                end
            end
        end
        return "{" .. table.concat(Entries, ", ") .. "}"
    elseif Constant.Kind == "Import" then
        local Import = Constant.Value
        local Length = math.floor(Import / 1073741824) % 4
        local Parts = {}
        local Masks = {math.floor(Import / 1048576) % 1024, math.floor(Import / 1024) % 1024, Import % 1024}
        if Length < 1 or Length > 3 then
            error("Import constant has an invalid path length", 0)
        end
        for Index = 1, Length do
            local Part = GetConstant(Proto, Masks[Index])
            local Key = Part.Kind == "String" and Part.Value or nil
            if type(Key) ~= "string" then
                error("Import constant references a non-string constant", 0)
            end
            if IsIdentifier(Key) then
                Parts[#Parts + 1] = Key
            else
                if #Parts == 0 then
                    Parts[#Parts + 1] = "_G[" .. Quote(Key) .. "]"
                else
                    Parts[#Parts + 1] = "[" .. Quote(Key) .. "]"
                end
            end
        end
        local Result = Parts[1]
        for Index = 2, #Parts do
            if Parts[Index]:sub(1, 1) == "[" then
                Result = Result .. Parts[Index]
            else
                Result = Result .. "." .. Parts[Index]
            end
        end
        return Result
    end
    error("Constant type " .. tostring(Constant.Kind) .. " cannot be reconstructed directly", 0)
end
local function GetDebugLocalName(Proto, Register, PC, UsedNames, UsePascalCase)
    for _, Local in ipairs(Proto.DebugLocals) do
        if Local.Register == Register and Local.StartPC <= PC and Local.EndPC > PC and type(Local.Name) == "string" and Local.Name ~= "" then
            local Base = UsePascalCase and PascalCase(Local.Name) or (IsIdentifier(Local.Name) and Local.Name or PascalCase(Local.Name))
            local Name = Base
            local Suffix = 2
            while UsedNames[Name] do
                Name = Base .. tostring(Suffix)
                Suffix = Suffix + 1
            end
            UsedNames[Name] = true
            return Name
        end
    end
    local Base = Register < Proto.NumParams and ("Argument" .. tostring(Register + 1)) or ("Temp" .. tostring(Register + 1))
    local Name = Base
    local Suffix = 2
    while UsedNames[Name] do
        Name = Base .. tostring(Suffix)
        Suffix = Suffix + 1
    end
    UsedNames[Name] = true
    return Name
end
local function IsIdentifierPath(Value)
    if Value == "" or Value:sub(1, 1) == "." or Value:sub(-1) == "." or Value:find("..", 1, true) then
        return false
    end
    for Part in Value:gmatch("[^%.]+") do
        if not Part:match("^[%a_][%w_]*$") then
            return false
        end
    end
    return true
end
local function IsSimpleTemporaryValue(Value)
    local Text = tostring(Value or ""):match("^%s*(.-)%s*$")
    if Text == "" or Text == "nil" or Text == "true" or Text == "false" then
        return Text ~= ""
    end
    if IsIdentifierPath(Text) then
        return true
    end
    if Text:match("^0[xX][%da-fA-F]+$") or Text:match("^[%+%-]?%d+%.?%d*[eE]?[%+%-]?%d*$") or Text:match("^[%+%-]?%.%d+[eE]?[%+%-]?%d*$") then
        return tonumber(Text) ~= nil
    end
    local QuoteCharacter = Text:sub(1, 1)
    if QuoteCharacter ~= "\"" and QuoteCharacter ~= "'" then
        return false
    end
    local Index = 2
    while Index <= #Text do
        local Character = Text:sub(Index, Index)
        if Character == "\\" then
            Index = Index + 2
        elseif Character == QuoteCharacter then
            return Index == #Text
        else
            Index = Index + 1
        end
    end
    return false
end
local function GetAssignmentParts(Line)
    local Indentation = Line:match("^(%s*)") or ""
    local Body = Line:sub(#Indentation + 1)
    local Left, Right = Body:match("^([^=]+)%s*=%s*(.-)%s*$")
    if not Left then
        return nil
    end
    Left = Left:match("^%s*(.-)%s*$")
    if Left:match("^local%s") or Left:match("^function%s") then
        return nil
    end
    local Names = {}
    for Name in Left:gmatch("[%a_][%w_]*") do
        Names[#Names + 1] = Name
    end
    if #Names == 0 then
        return nil
    end
    if Left:gsub("%s+", "") ~= table.concat(Names, ",") then
        return nil
    end
    return {
        Indentation = Indentation,
        Left = Left,
        Right = Right,
        Names = Names
    }
end
local function IsFieldIdentifier(Text, StartIndex)
    local PreviousIndex = StartIndex - 1
    while PreviousIndex > 0 and Text:sub(PreviousIndex, PreviousIndex):match("%s") do
        PreviousIndex = PreviousIndex - 1
    end
    local PreviousCharacter = Text:sub(PreviousIndex, PreviousIndex)
    return PreviousCharacter == "." or PreviousCharacter == ":"
end
local function CountCodeIdentifier(Line, TargetName)
    local Count = 0
    local Index = 1
    while Index <= #Line do
        local Character = Line:sub(Index, Index)
        if Character == "\"" or Character == "'" then
            local QuoteCharacter = Character
            Index = Index + 1
            while Index <= #Line do
                Character = Line:sub(Index, Index)
                if Character == "\\" then
                    Index = Index + 2
                elseif Character == QuoteCharacter then
                    Index = Index + 1
                    break
                else
                    Index = Index + 1
                end
            end
        elseif Character == "-" and Line:sub(Index + 1, Index + 1) == "-" then
            break
        elseif Character:match("[%a_]") then
            local StartIndex = Index
            Index = Index + 1
            while Index <= #Line and Line:sub(Index, Index):match("[%w_]") do
                Index = Index + 1
            end
            if Line:sub(StartIndex, Index - 1) == TargetName and not IsFieldIdentifier(Line, StartIndex) then
                Count = Count + 1
            end
        else
            Index = Index + 1
        end
    end
    return Count
end
local function ReplaceCodeIdentifier(Line, TargetName, Replacement)
    local Output = {}
    local Index = 1
    while Index <= #Line do
        local Character = Line:sub(Index, Index)
        if Character == "\"" or Character == "'" then
            local StartIndex = Index
            local QuoteCharacter = Character
            Index = Index + 1
            while Index <= #Line do
                Character = Line:sub(Index, Index)
                if Character == "\\" then
                    Index = Index + 2
                elseif Character == QuoteCharacter then
                    Index = Index + 1
                    break
                else
                    Index = Index + 1
                end
            end
            Output[#Output + 1] = Line:sub(StartIndex, Index - 1)
        elseif Character == "-" and Line:sub(Index + 1, Index + 1) == "-" then
            Output[#Output + 1] = Line:sub(Index)
            break
        elseif Character:match("[%a_]") then
            local StartIndex = Index
            Index = Index + 1
            while Index <= #Line and Line:sub(Index, Index):match("[%w_]") do
                Index = Index + 1
            end
            local Identifier = Line:sub(StartIndex, Index - 1)
            Output[#Output + 1] = Identifier == TargetName and not IsFieldIdentifier(Line, StartIndex) and Replacement or Identifier
        else
            Output[#Output + 1] = Character
            Index = Index + 1
        end
    end
    return table.concat(Output)
end
local function GetExpressionIdentifiers(Expression)
    local Identifiers = {}
    local Index = 1
    while Index <= #Expression do
        local Character = Expression:sub(Index, Index)
        if Character == "\"" or Character == "'" then
            local QuoteCharacter = Character
            Index = Index + 1
            while Index <= #Expression do
                Character = Expression:sub(Index, Index)
                if Character == "\\" then
                    Index = Index + 2
                elseif Character == QuoteCharacter then
                    Index = Index + 1
                    break
                else
                    Index = Index + 1
                end
            end
        elseif Character:match("[%a_]") then
            local StartIndex = Index
            Index = Index + 1
            while Index <= #Expression and Expression:sub(Index, Index):match("[%w_]") do
                Index = Index + 1
            end
            if not IsFieldIdentifier(Expression, StartIndex) then
                Identifiers[Expression:sub(StartIndex, Index - 1)] = true
            end
        else
            Index = Index + 1
        end
    end
    return Identifiers
end
local function TryInlineTemporary(Lines, SourceIndex)
    local SourceAssignment = GetAssignmentParts(Lines[SourceIndex])
    if not SourceAssignment or #SourceAssignment.Names ~= 1 or not IsSimpleTemporaryValue(SourceAssignment.Right) then
        return false
    end
    local TargetName = SourceAssignment.Names[1]
    if SourceAssignment.Right == TargetName then
        return false
    end
    local Dependencies = GetExpressionIdentifiers(SourceAssignment.Right)
    local SearchLimit = math.min(#Lines, SourceIndex + 96)
    for TargetIndex = SourceIndex + 1, SearchLimit do
        local TargetLine = Lines[TargetIndex]
        if TargetLine == "" or TargetLine:match("^%s*%-%-") then
            continue
        end
        local TargetIndentation = TargetLine:match("^(%s*)") or ""
        if TargetIndentation ~= SourceAssignment.Indentation then
            break
        end
        local TargetAssignment = GetAssignmentParts(TargetLine)
        if TargetAssignment then
            local RightUses = CountCodeIdentifier(TargetAssignment.Right, TargetName)
            local WritesTarget = false
            for _, Name in ipairs(TargetAssignment.Names) do
                if Name == TargetName then
                    WritesTarget = true
                    break
                end
            end
            if WritesTarget then
                if RightUses == 1 then
                    Lines[TargetIndex] = TargetAssignment.Indentation .. TargetAssignment.Left .. " = " .. ReplaceCodeIdentifier(TargetAssignment.Right, TargetName, SourceAssignment.Right)
                    table.remove(Lines, SourceIndex)
                    return true
                end
                return false
            end
            if RightUses > 0 then
                if RightUses == 1 then
                    Lines[TargetIndex] = TargetAssignment.Indentation .. TargetAssignment.Left .. " = " .. ReplaceCodeIdentifier(TargetAssignment.Right, TargetName, SourceAssignment.Right)
                    table.remove(Lines, SourceIndex)
                    return true
                end
                return false
            end
            if not IsSimpleTemporaryValue(TargetAssignment.Right) then
                return false
            end
            for _, Name in ipairs(TargetAssignment.Names) do
                if Dependencies[Name] then
                    return false
                end
            end
        else
            local Uses = CountCodeIdentifier(TargetLine, TargetName)
            if Uses == 1 then
                Lines[TargetIndex] = ReplaceCodeIdentifier(TargetLine, TargetName, SourceAssignment.Right)
                table.remove(Lines, SourceIndex)
                return true
            end
            return false
        end
    end
    return false
end
local function RemoveUnusedLocalNames(Lines)
    local Index = 1
    while Index <= #Lines do
        local Indentation, Declaration = Lines[Index]:match("^(%s*)local%s+(.+)$")
        if not Declaration or Declaration:find("=", 1, true) or Declaration:find("function", 1, true) then
            Index = Index + 1
            continue
        end
        local Names = {}
        for Name in Declaration:gmatch("[^,]+") do
            Name = Name:match("^%s*(.-)%s*$")
            if not Name:match("^[%a_][%w_]*$") then
                Names = {}
                break
            end
            Names[#Names + 1] = Name
        end
        if #Names == 0 then
            Index = Index + 1
            continue
        end
        local KeptNames = {}
        for _, Name in ipairs(Names) do
            local References = 0
            for _, Line in ipairs(Lines) do
                References = References + CountCodeIdentifier(Line, Name)
                if References > 1 then
                    break
                end
            end
            if References > 1 then
                KeptNames[#KeptNames + 1] = Name
            end
        end
        if #KeptNames == #Names then
            Index = Index + 1
        elseif #KeptNames == 0 then
            table.remove(Lines, Index)
        else
            Lines[Index] = Indentation .. "local " .. table.concat(KeptNames, ", ")
            Index = Index + 1
        end
    end
end
local function OptimizeTemporaryAssignments(Source)
    local Lines = {}
    for Line in (tostring(Source or "") .. "\n"):gmatch("(.-)\n") do
        Lines[#Lines + 1] = Line
    end
    local Index = 1
    local OptimizationCount = 0
    while Index <= #Lines do
        if TryInlineTemporary(Lines, Index) then
            OptimizationCount = OptimizationCount + 1
        else
            Index = Index + 1
        end
    end
    RemoveUnusedLocalNames(Lines)
    local CleanLines = {}
    for _, Line in ipairs(Lines) do
        if Line ~= "" or #CleanLines == 0 or CleanLines[#CleanLines] ~= "" then
            CleanLines[#CleanLines + 1] = Line
        end
    end
    while #CleanLines > 0 and CleanLines[#CleanLines] == "" do
        table.remove(CleanLines)
    end
    return table.concat(CleanLines, "\n")
end

local function ReconstructLinear(Proto, Strings, Options, Parsed, CaptureNames, Depth)
    local UsePascalCase = not Options or Options.PascalCase ~= false
    local CurrentDepth = Depth or 0
    if CurrentDepth > 64 then
        return nil, "Nested function depth exceeds the reconstruction limit"
    end
    CaptureNames = CaptureNames or {}
    local Lines = {}
    local IndentLevel = 0
    local CurrentPC = 0
    local ActiveInstructionIndex = 1
    local function EmitLine(Value)
        local Text = string.rep("    ", IndentLevel) .. tostring(Value)
        local IsSectionStart = IndentLevel == 0 and (
            Text:match("^local function[%s]") ~= nil
            or Text:match("^function[%s]") ~= nil
            or Text:match("^local [%a_][%w_]*%s*=%s*function[%s%(]") ~= nil
            or Text:match("^[%a_][%w_]*%s*=%s*function[%s%(]") ~= nil
            or Text == "return" or Text:match("^return%s") ~= nil
        )
        if IsSectionStart and #Lines > 0 and Lines[#Lines] ~= "" then
            Lines[#Lines + 1] = ""
        end
        Lines[#Lines + 1] = Text
    end
    local RegisterReads = {}
    local RegisterWrites = {}
    local function AddRegisterUse(Target, Register)
        if type(Register) == "number" and Register >= 0 and Register < Proto.MaxStackSize then
            Target[Register] = true
        end
    end
    local function AddRegisterRange(Target, First, Last)
        for Register = First, math.min(Last, Proto.MaxStackSize - 1) do
            AddRegisterUse(Target, Register)
        end
    end
    for ItemIndex, Item in ipairs(Proto.Instructions) do
        local ItemName = Item.Name
        local ItemA = Item.A
        local ItemB = Item.B
        local ItemC = Item.C
        local Reads = {}
        local Writes = {}
        if ItemName == "MOVE" or ItemName == "SETGLOBAL" or ItemName == "SETUPVAL" or ItemName == "NOT" or ItemName == "MINUS" or ItemName == "LENGTH" then
            AddRegisterUse(Reads, ItemName == "MOVE" and ItemB or ItemA)
        elseif ItemName == "GETTABLEKS" or ItemName == "GETTABLEN" or ItemName == "GETUDATAKS" then
            AddRegisterUse(Reads, ItemB)
        elseif ItemName == "GETTABLE" then
            AddRegisterUse(Reads, ItemB)
            AddRegisterUse(Reads, ItemC)
        elseif ItemName == "SETTABLE" then
            AddRegisterUse(Reads, ItemA)
            AddRegisterUse(Reads, ItemB)
            AddRegisterUse(Reads, ItemC)
        elseif ItemName == "SETTABLEKS" or ItemName == "SETTABLEN" or ItemName == "SETUDATAKS" then
            AddRegisterUse(Reads, ItemA)
            AddRegisterUse(Reads, ItemB)
        elseif ItemName == "ADD" or ItemName == "SUB" or ItemName == "MUL" or ItemName == "DIV" or ItemName == "MOD" or ItemName == "POW" or ItemName == "IDIV" or ItemName == "AND" or ItemName == "OR" or ItemName == "CONCAT" then
            AddRegisterRange(Reads, ItemB, ItemC)
        elseif ItemName == "ADDK" or ItemName == "SUBK" or ItemName == "MULK" or ItemName == "DIVK" or ItemName == "MODK" or ItemName == "POWK" or ItemName == "IDIVK" or ItemName == "ANDK" or ItemName == "ORK" then
            AddRegisterUse(Reads, ItemB)
        elseif ItemName == "SUBRK" or ItemName == "DIVRK" then
            AddRegisterUse(Reads, ItemC)
        elseif ItemName == "NAMECALL" or ItemName == "NAMECALLUDATA" then
            AddRegisterUse(Reads, ItemB)
        elseif ItemName == "CALL" or ItemName == "CALLFB" then
            AddRegisterUse(Reads, ItemA)
            if ItemB == 0 then
                AddRegisterRange(Reads, ItemA + 1, Proto.MaxStackSize - 1)
            elseif ItemB > 1 then
                AddRegisterRange(Reads, ItemA + 1, ItemA + ItemB - 1)
            end
        elseif ItemName == "RETURN" then
            if ItemB == 0 then
                AddRegisterRange(Reads, ItemA, Proto.MaxStackSize - 1)
            elseif ItemB > 1 then
                AddRegisterRange(Reads, ItemA, ItemA + ItemB - 2)
            end
        elseif ItemName == "SETLIST" then
            AddRegisterUse(Reads, ItemA)
            if ItemC == 0 then
                AddRegisterRange(Reads, ItemB, Proto.MaxStackSize - 1)
            elseif ItemC > 1 then
                AddRegisterRange(Reads, ItemB, ItemB + ItemC - 2)
            end
        elseif ItemName == "JUMPIF" or ItemName == "JUMPIFNOT" or ItemName == "JUMPIFEQ" or ItemName == "JUMPIFLE" or ItemName == "JUMPIFLT" or ItemName == "JUMPIFNOTEQ" or ItemName == "JUMPIFNOTLE" or ItemName == "JUMPIFNOTLT" or ItemName == "JUMPXEQKNIL" or ItemName == "JUMPXEQKB" or ItemName == "JUMPXEQKN" or ItemName == "JUMPXEQKS" then
            AddRegisterUse(Reads, ItemA)
            if Item.Aux and (ItemName == "JUMPIFEQ" or ItemName == "JUMPIFLE" or ItemName == "JUMPIFLT" or ItemName == "JUMPIFNOTEQ" or ItemName == "JUMPIFNOTLE" or ItemName == "JUMPIFNOTLT") then
                AddRegisterUse(Reads, Item.Aux % 256)
            end
        elseif ItemName == "FORNPREP" or ItemName == "FORNLOOP" or ItemName == "FORGLOOP" then
            AddRegisterRange(Reads, ItemA, ItemA + 2)
        elseif ItemName == "CAPTURE" and (ItemA == 0 or ItemA == 1) then
            AddRegisterUse(Reads, ItemB)
        end
        if ItemName == "LOADNIL" or ItemName == "LOADB" or ItemName == "LOADN" or ItemName == "LOADK" or ItemName == "LOADKX" or ItemName == "MOVE" or ItemName == "GETGLOBAL" or ItemName == "GETUPVAL" or ItemName == "GETTABLE" or ItemName == "GETTABLEKS" or ItemName == "GETTABLEN" or ItemName == "GETUDATAKS" or ItemName == "ADD" or ItemName == "SUB" or ItemName == "MUL" or ItemName == "DIV" or ItemName == "MOD" or ItemName == "POW" or ItemName == "IDIV" or ItemName == "AND" or ItemName == "OR" or ItemName == "ADDK" or ItemName == "SUBK" or ItemName == "MULK" or ItemName == "DIVK" or ItemName == "MODK" or ItemName == "POWK" or ItemName == "IDIVK" or ItemName == "ANDK" or ItemName == "ORK" or ItemName == "SUBRK" or ItemName == "DIVRK" or ItemName == "NOT" or ItemName == "MINUS" or ItemName == "LENGTH" or ItemName == "CONCAT" or ItemName == "NEWTABLE" or ItemName == "DUPTABLE" or ItemName == "GETIMPORT" or ItemName == "NEWCLOSURE" or ItemName == "DUPCLOSURE" then
            AddRegisterUse(Writes, ItemA)
        elseif ItemName == "NAMECALL" or ItemName == "NAMECALLUDATA" then
            AddRegisterUse(Writes, ItemA)
            AddRegisterUse(Writes, ItemA + 1)
        elseif ItemName == "CALL" or ItemName == "CALLFB" then
            if ItemC == 0 then
                AddRegisterRange(Writes, ItemA, Proto.MaxStackSize - 1)
            elseif ItemC > 1 then
                AddRegisterRange(Writes, ItemA, ItemA + ItemC - 2)
            end
        elseif ItemName == "GETVARARGS" then
            if ItemB == 0 then
                AddRegisterRange(Writes, ItemA, Proto.MaxStackSize - 1)
            elseif ItemB > 1 then
                AddRegisterRange(Writes, ItemA, ItemA + ItemB - 2)
            end
        elseif ItemName == "FORNPREP" or ItemName == "FORNLOOP" or ItemName == "FORGPREP" or ItemName == "FORGPREP_INEXT" or ItemName == "FORGPREP_NEXT" or ItemName == "FORGLOOP" then
            AddRegisterRange(Writes, ItemA, ItemA + 3)
        end
        RegisterReads[ItemIndex] = Reads
        RegisterWrites[ItemIndex] = Writes
        YieldControl()
    end
    local RegisterUseCountsByInstruction = {}
    local UsesAfterWrite = {}
    for ItemIndex = #Proto.Instructions, 1, -1 do
        local Writes = RegisterWrites[ItemIndex]
        local UsesForInstruction = {}
        for Register in pairs(Writes) do
            UsesForInstruction[Register] = UsesAfterWrite[Register] or 0
            UsesAfterWrite[Register] = 0
        end
        for Register in pairs(RegisterReads[ItemIndex]) do
            UsesAfterWrite[Register] = (UsesAfterWrite[Register] or 0) + 1
        end
        RegisterUseCountsByInstruction[ItemIndex] = UsesForInstruction
    end
    local Registers = {}
    local Declared = {}
    local UsedNames = {}
    local TopDeclarations = {}
    local TopDeclarationSet = {}
    for _, CaptureName in pairs(CaptureNames) do
        UsedNames[CaptureName] = true
    end
    local NameCalls = {}
    local RegisterExpressions = {}
    local RegisterInline = {}
    local KnownValues = {}
    local KnownValueFlags = {}
    local RegisterWritten = {}
    local RegisterDebugLocals = {}
    local DebugLocalNames = {}
    local function GetFreshRegisterName(BaseName)
        local Base = UsePascalCase and PascalCase(BaseName) or (IsIdentifier(BaseName) and BaseName or PascalCase(BaseName))
        local Name = Base
        local Suffix = 2
        while UsedNames[Name] do
            Name = Base .. tostring(Suffix)
            Suffix = Suffix + 1
        end
        UsedNames[Name] = true
        return Name
    end
    local function GetActiveDebugLocal(Register, PC)
        for _, Local in ipairs(Proto.DebugLocals) do
            if Local.Register == Register and Local.StartPC <= PC and Local.EndPC > PC and type(Local.Name) == "string" and Local.Name ~= "" then
                return Local
            end
        end
        return nil
    end
    local function RefreshRegisterLocal(Register, PC)
        local ActiveLocal = GetActiveDebugLocal(Register, PC or CurrentPC)
        local PreviousLocal = RegisterDebugLocals[Register]
        if ActiveLocal == PreviousLocal then
            return
        end
        RegisterDebugLocals[Register] = ActiveLocal
        if not ActiveLocal then
            if Register >= Proto.NumParams then
                Registers[Register] = nil
                RegisterExpressions[Register] = nil
                RegisterInline[Register] = false
                KnownValues[Register] = nil
                KnownValueFlags[Register] = false
                RegisterWritten[Register] = false
                Declared[Register] = false
            end
            return
        end
        local Name = DebugLocalNames[ActiveLocal]
        if not Name then
            local Base = UsePascalCase and PascalCase(ActiveLocal.Name) or (IsIdentifier(ActiveLocal.Name) and ActiveLocal.Name or PascalCase(ActiveLocal.Name))
            Name = GetFreshRegisterName(Base)
            DebugLocalNames[ActiveLocal] = Name
        end
        Registers[Register] = Name
        RegisterExpressions[Register] = Name
        RegisterInline[Register] = false
        KnownValues[Register] = nil
        KnownValueFlags[Register] = false
        RegisterWritten[Register] = false
        Declared[Register] = false
    end
    local HighestRegister = Proto.NumParams - 1
    local MultiValue = nil
    local MultiValueStart = nil
    local Params = {}
    for Register = 0, Proto.NumParams - 1 do
        local Name = GetDebugLocalName(Proto, Register, 0, UsedNames, UsePascalCase)
        Params[#Params + 1] = Name
        Registers[Register] = Name
        RegisterExpressions[Register] = Name
        local ActiveLocal = GetActiveDebugLocal(Register, 0)
        if ActiveLocal then
            RegisterDebugLocals[Register] = ActiveLocal
            DebugLocalNames[ActiveLocal] = Name
        end
        Declared[Register] = true
        RegisterWritten[Register] = true
        HighestRegister = math.max(HighestRegister, Register)
    end
    local function GetReg(Register, PC)
        RefreshRegisterLocal(Register, PC or CurrentPC)
        if RegisterInline[Register] then
            return RegisterExpressions[Register] or "nil"
        end
        local Value = Registers[Register]
        if not Value then
            local DebugName = GetDebugLocalName(Proto, Register, PC or CurrentPC, UsedNames, UsePascalCase)
            Registers[Register] = DebugName
            return DebugName
        end
        return Value
    end
    local function GetRegExpression(Register)
        RefreshRegisterLocal(Register, CurrentPC)
        if RegisterInline[Register] then
            return RegisterExpressions[Register] or "nil"
        end
        return RegisterExpressions[Register] or GetReg(Register)
    end
    local function FormatKnownValue(Value)
        if Value == nil then
            return "nil"
        elseif type(Value) == "string" then
            return Quote(Value)
        elseif type(Value) == "boolean" then
            return Value and "true" or "false"
        elseif type(Value) == "number" then
            if Value ~= Value or Value == math.huge or Value == -math.huge then
                return nil
            end
            return tostring(Value)
        end
        return nil
    end
    local function IsGenericDebugName(Name)
        local Lower = string.lower(tostring(Name or ""))
        return Lower == "variable"
            or Lower == "callback"
            or Lower == "instance"
            or Lower == "function"
            or Lower == "anonymous"
            or Lower == "closure"
            or Lower == "pcall"
            or Lower == "xpcall"
            or Lower:match("^arg%d+$") ~= nil
            or Lower:match("^local%d+$") ~= nil
            or Lower:match("^var%d+$") ~= nil
            or Lower:match("^v%d+$") ~= nil
            or Lower:match("^temp%d+$") ~= nil
            or Lower:match("^tmp%d+$") ~= nil
            or Lower:match("^pcall%d+$") ~= nil
            or Lower:match("^xpcall%d+$") ~= nil
            or Lower:match("^function%d+$") ~= nil
            or Lower:match("^closure%d+$") ~= nil
            or Lower:match("^proto%d+$") ~= nil
    end
    local MethodResultNames = {
        GetChildren = "Children",
        GetDescendants = "Descendants",
        GetPlayers = "Players",
        GetPlayerFromCharacter = "Player",
        GetCharacterFromPlayer = "Character",
        GetHumanoid = "Humanoid",
        GetRootPart = "RootPart",
        GetAttributes = "Attributes",
        GetAttribute = "Attribute",
        GetAttributeChangedSignal = "AttributeChangedSignal",
        GetFullName = "FullName",
        GetName = "Name",
        GetPivot = "Pivot",
        GetPrimaryPartCFrame = "PrimaryPartCFrame",
        GetDebugId = "DebugId",
        GetMouse = "Mouse",
        GetMouseLocation = "MouseLocation",
        GetProductInfo = "ProductInfo",
        GetUserThumbnailAsync = "Thumbnail",
        GetUserIdFromNameAsync = "UserId",
        GetNameFromUserIdAsync = "Username",
        GetRankInGroup = "Rank",
        GetRoleInGroup = "Role",
        GetGroupInfoAsync = "GroupInfo",
        GetJoinData = "JoinData",
        GetTagged = "TaggedInstances",
        GetTags = "Tags",
        GetPropertyChangedSignal = "PropertyChangedSignal",
        FindFirstAncestor = "Ancestor",
        FindFirstAncestorOfClass = "Ancestor",
        FindFirstAncestorWhichIsA = "Ancestor",
        FindFirstChild = "Child",
        FindFirstChildOfClass = "Child",
        FindFirstChildWhichIsA = "Child",
        WaitForChild = "Child",
        GetBoundingBox = "BoundingBox",
        GetExtentsSize = "ExtentsSize",
        GetAsync = "Response",
        PostAsync = "Response",
        HttpGet = "Response",
        RequestAsync = "Response",
        JSONDecode = "DecodedData",
        JSONEncode = "EncodedData",
        Connect = "Connection",
        Once = "Connection",
        Clone = "Clone"
    }
    local function InferRegisterName(Expression, Register)
        local AttributeName = Expression:match('GetAttribute%s*%(%s*"([^"]+)"')
        if AttributeName and AttributeName ~= "" then
            return PascalCase(AttributeName)
        end
        local AttributeSignalName = Expression:match('GetAttributeChangedSignal%s*%(%s*"([^"]+)"')
        if AttributeSignalName and AttributeSignalName ~= "" then
            return PascalCase(AttributeSignalName) .. "Changed"
        end
        local PropertySignalName = Expression:match('GetPropertyChangedSignal%s*%(%s*"([^"]+)"')
        if PropertySignalName and PropertySignalName ~= "" then
            return PascalCase(PropertySignalName) .. "Changed"
        end
        local ServiceName = Expression:match('GetService%s*%(%s*"([^"]+)"')
        if ServiceName and ServiceName ~= "" then
            return PascalCase(ServiceName)
        end
        local ClassName = Expression:match('Instance%.new%s*%(%s*"([^"]+)"')
        if ClassName and ClassName ~= "" then
            return PascalCase(ClassName)
        end
        local ChildName = Expression:match('WaitForChild%s*%(%s*"([^"]+)"')
            or Expression:match('FindFirstChild%s*%(%s*"([^"]+)"')
        if ChildName and ChildName ~= "" then
            return PascalCase(ChildName)
        end
        local IndexedName = Expression:match('%[%s*"([^"]+)"%s*%]$')
        if IndexedName and IndexedName ~= "" then
            return PascalCase(IndexedName)
        end
        local MethodName = Expression:match("[:%.]([%a_][%w_]*)%s*%(")
        local MethodResult = MethodName and MethodResultNames[MethodName]
        if MethodResult then
            return PascalCase(MethodResult)
        end
        if Expression == "game" then
            return "Game"
        elseif Expression == "workspace" then
            return "Workspace"
        elseif Expression == "script" then
            return "Script"
        elseif Expression:match("^function[%s%(]") then
            return "Callback"
        elseif Expression == "..." then
            return "Arguments"
        end
        local EnumItem = Expression:match("^Enum%.[%w_]+%.([%w_]+)$")
        if EnumItem then
            return PascalCase(EnumItem)
        end
        local Property = Expression:match("%.([%a_][%w_]*)$")
        if Property and Property ~= "new" then
            return PascalCase(Property)
        end
        local Identifier = Expression:match("^([%a_][%w_]*)$")
        if Identifier then
            return PascalCase(Identifier)
        end
        return "Local" .. tostring(Register + 1)
    end
    local function DeclareRegister(Register, PC, AllowInlineDeclaration)
        RefreshRegisterLocal(Register, PC)
        local Name = Registers[Register]
        if not Name then
            Name = GetFreshRegisterName(InferRegisterName(RegisterExpressions[Register] or "Value", Register))
            Registers[Register] = Name
        end
        if not Declared[Register] then
            if not (AllowInlineDeclaration and IndentLevel == 0) and not TopDeclarationSet[Name] then
                TopDeclarationSet[Name] = true
                TopDeclarations[#TopDeclarations + 1] = Name
            end
            Declared[Register] = true
        end
        return Name
    end
    local function HasNamedDebugLocal(Register, PC)
        for _, Local in ipairs(Proto.DebugLocals) do
            if Local.Register == Register and Local.StartPC <= PC and Local.EndPC > PC and type(Local.Name) == "string" and Local.Name ~= "" and not IsGenericDebugName(Local.Name) then
                return true
            end
        end
        return false
    end
    local function WriteReg(Register, Expression, PC, KnownValue, IsKnown, ExpressionValue, InlineCandidate)
        RefreshRegisterLocal(Register, PC)
        local ActiveLocal = GetActiveDebugLocal(Register, PC)
        if not ActiveLocal and Register >= Proto.NumParams and (RegisterWritten[Register] or RegisterInline[Register] or Declared[Register]) then
            local BaseName = InferRegisterName(ExpressionValue or Expression, Register)
            Registers[Register] = GetFreshRegisterName(BaseName)
            RegisterExpressions[Register] = Registers[Register]
            RegisterInline[Register] = false
            KnownValues[Register] = nil
            KnownValueFlags[Register] = false
            RegisterWritten[Register] = false
            Declared[Register] = false
        end
        local CurrentInstruction = Proto.Instructions[ActiveInstructionIndex]
        local IsImmutableSource = CurrentInstruction
            and (CurrentInstruction.Name == "GETGLOBAL" or CurrentInstruction.Name == "GETIMPORT" or CurrentInstruction.Name == "GETUPVAL")
        local IsLiteralSource = CurrentInstruction
            and (CurrentInstruction.Name == "LOADNIL" or CurrentInstruction.Name == "LOADB" or CurrentInstruction.Name == "LOADN" or CurrentInstruction.Name == "LOADK" or CurrentInstruction.Name == "LOADKX")
            and IsKnown == true
            and (KnownValue == nil or type(KnownValue) == "string" or type(KnownValue) == "boolean" or type(KnownValue) == "number")
        local UseCount = RegisterUseCountsByInstruction[ActiveInstructionIndex] and RegisterUseCountsByInstruction[ActiveInstructionIndex][Register] or 0
        local CanInline = InlineCandidate == true
            and (UseCount == 1 or IsImmutableSource or IsLiteralSource)
            and not Declared[Register]
            and not RegisterWritten[Register]
            and not HasNamedDebugLocal(Register, PC)
        HighestRegister = math.max(HighestRegister, Register)
        RegisterExpressions[Register] = ExpressionValue or Expression
        RegisterInline[Register] = CanInline
        KnownValueFlags[Register] = IsKnown == true
        if IsKnown == true then
            KnownValues[Register] = KnownValue
        else
            KnownValues[Register] = nil
        end
        if CanInline then
            return nil
        end
        local ExistingName = Registers[Register]
        if not ExistingName then
            ExistingName = GetDebugLocalName(Proto, Register, PC, UsedNames, UsePascalCase)
            Registers[Register] = ExistingName
        end
        if Register >= Proto.NumParams and not RegisterWritten[Register] and not Declared[Register] and IsGenericDebugName(ExistingName) and (not ActiveLocal or IsGenericDebugName(ActiveLocal.Name)) then
            local BaseName = InferRegisterName(ExpressionValue or Expression, Register)
            local ExistingBase = ActiveLocal and PascalCase(ActiveLocal.Name) or nil
            if ExistingBase ~= BaseName then
                Registers[Register] = GetFreshRegisterName(BaseName)
                if ActiveLocal then
                    DebugLocalNames[ActiveLocal] = Registers[Register]
                end
            end
        end
        local WasDeclared = Declared[Register] == true
        RegisterWritten[Register] = true
        RegisterInline[Register] = false
        local Name = DeclareRegister(Register, PC, IndentLevel == 0)
        HighestRegister = math.max(HighestRegister, Register)
        RegisterExpressions[Register] = Name
        KnownValueFlags[Register] = IsKnown == true
        if IsKnown == true then
            KnownValues[Register] = KnownValue
        else
            KnownValues[Register] = nil
        end
        if (WasDeclared or IndentLevel > 0) and Name == Expression then
            return Name
        end
        if not WasDeclared and IndentLevel == 0 then
            EmitLine("local " .. Name .. " = " .. Expression)
        else
            EmitLine(Name .. " = " .. Expression)
        end
        return Name
    end
    local function InvalidateRegister(Register, Name)
        RegisterInline[Register] = false
        KnownValueFlags[Register] = false
        KnownValues[Register] = nil
        if Name then
            RegisterWritten[Register] = true
            Registers[Register] = Name
            RegisterExpressions[Register] = Name
        else
            RegisterExpressions[Register] = nil
        end
    end
    local function GetConstantKnown(Constant)
        if Constant.Kind == "Nil" then
            return nil, true
        elseif Constant.Kind == "Boolean" or Constant.Kind == "Number" or Constant.Kind == "String" then
            return Constant.Value, true
        elseif Constant.Kind == "Integer" then
            local Value = tonumber(Constant.Value)
            if Value and math.abs(Value) <= 9007199254740991 then
                return Value, true
            end
        end
        return nil, false
    end
    local function TryFoldBinary(Name, LeftValue, RightValue)
        local Operations = {
            ADD = function(Left, Right) return Left + Right end,
            SUB = function(Left, Right) return Left - Right end,
            MUL = function(Left, Right) return Left * Right end,
            DIV = function(Left, Right) return Left / Right end,
            MOD = function(Left, Right) return Left % Right end,
            POW = function(Left, Right) return Left ^ Right end,
            IDIV = function(Left, Right) return Left // Right end,
            AND = function(Left, Right) return Left and Right end,
            OR = function(Left, Right) return Left or Right end
        }
        local Operation = Operations[Name]
        if not Operation then
            return false, nil
        end
        local Success, Result = pcall(Operation, LeftValue, RightValue)
        if not Success or FormatKnownValue(Result) == nil then
            return false, nil
        end
        return true, Result
    end
    local function TryFoldCall(FunctionExpression, Arguments, ArgumentCount)
        local StringLibrary = string
        local MathLibrary = math
        local BitLibrary = bit32
        local Functions = {
            ["string.char"] = StringLibrary and StringLibrary.char,
            ["string.reverse"] = StringLibrary and StringLibrary.reverse,
            ["string.lower"] = StringLibrary and StringLibrary.lower,
            ["string.upper"] = StringLibrary and StringLibrary.upper,
            ["string.sub"] = StringLibrary and StringLibrary.sub,
            ["string.rep"] = StringLibrary and StringLibrary.rep,
            ["string.byte"] = StringLibrary and StringLibrary.byte,
            ["string.format"] = StringLibrary and StringLibrary.format,
            ["string.match"] = StringLibrary and StringLibrary.match,
            ["tonumber"] = tonumber,
            ["tostring"] = tostring,
            ["math.abs"] = MathLibrary and MathLibrary.abs,
            ["math.ceil"] = MathLibrary and MathLibrary.ceil,
            ["math.floor"] = MathLibrary and MathLibrary.floor,
            ["math.max"] = MathLibrary and MathLibrary.max,
            ["math.min"] = MathLibrary and MathLibrary.min,
            ["math.sqrt"] = MathLibrary and MathLibrary.sqrt,
            ["math.sin"] = MathLibrary and MathLibrary.sin,
            ["math.cos"] = MathLibrary and MathLibrary.cos,
            ["math.tan"] = MathLibrary and MathLibrary.tan,
            ["math.exp"] = MathLibrary and MathLibrary.exp,
            ["math.log"] = MathLibrary and MathLibrary.log,
            ["math.fmod"] = MathLibrary and MathLibrary.fmod,
            ["math.clamp"] = MathLibrary and MathLibrary.clamp,
            ["math.sign"] = MathLibrary and MathLibrary.sign,
            ["bit32.band"] = BitLibrary and BitLibrary.band,
            ["bit32.bor"] = BitLibrary and BitLibrary.bor,
            ["bit32.bxor"] = BitLibrary and BitLibrary.bxor,
            ["bit32.bnot"] = BitLibrary and BitLibrary.bnot,
            ["bit32.lshift"] = BitLibrary and BitLibrary.lshift,
            ["bit32.rshift"] = BitLibrary and BitLibrary.rshift,
            ["bit32.arshift"] = BitLibrary and BitLibrary.arshift
        }
        local Callback = Functions[FunctionExpression]
        if type(Callback) ~= "function" then
            return false, nil
        end
        if FunctionExpression == "string.rep" then
            local RepeatCount = tonumber(Arguments[2]) or 0
            local InputLength = type(Arguments[1]) == "string" and #Arguments[1] or 0
            if RepeatCount < 0 or RepeatCount > 4096 or InputLength * RepeatCount > 65536 then
                return false, nil
            end
        elseif FunctionExpression == "string.format" then
            if type(Arguments[1]) ~= "string" or #Arguments[1] > 4096 then
                return false, nil
            end
        end
        local Unpack = table.unpack or unpack
        local Success, Result = pcall(Callback, Unpack(Arguments, 1, ArgumentCount or #Arguments))
        if not Success or FormatKnownValue(Result) == nil or (type(Result) == "string" and #Result > 65536) then
            return false, nil
        end
        return true, Result
    end
    local function GetProperty(Base, Property)
        if IsIdentifier(Property) then
            return Base .. "." .. Property
        end
        return Base .. "[" .. Quote(Property) .. "]"
    end
    local function GetUniqueName(Base)
        local Name = Base
        local Suffix = 2
        while UsedNames[Name] do
            Name = Base .. tostring(Suffix)
            Suffix = Suffix + 1
        end
        UsedNames[Name] = true
        return Name
    end
    local Instructions = Proto.Instructions
    local InstructionIndexByPc = {}
    for InstructionIndex, Instruction in ipairs(Instructions) do
        InstructionIndexByPc[Instruction.PC] = InstructionIndex
    end
    local function GetTargetIndex(Instruction)
        local TargetPc
        if Instruction.Name == "JUMPX" then
            TargetPc = Instruction.PC + Instruction.E + 1
        else
            TargetPc = Instruction.PC + Instruction.D + 1
        end
        return InstructionIndexByPc[TargetPc] or (#Instructions + 1)
    end
    local function GetFallthroughCondition(Instruction)
        local Name = Instruction.Name
        local A = GetReg(Instruction.A, Instruction.PC)
        if Name == "JUMPIF" then
            return "not (" .. A .. ")"
        elseif Name == "JUMPIFNOT" then
            return A
        elseif Name == "JUMPIFEQ" or Name == "JUMPIFLE" or Name == "JUMPIFLT" or Name == "JUMPIFNOTEQ" or Name == "JUMPIFNOTLE" or Name == "JUMPIFNOTLT" then
            local B = GetReg((Instruction.Aux or 0) % 256, Instruction.PC)
            if Name == "JUMPIFEQ" then
                return "(" .. A .. " ~= " .. B .. ")"
            elseif Name == "JUMPIFLE" then
                return "(" .. A .. " > " .. B .. ")"
            elseif Name == "JUMPIFLT" then
                return "(" .. A .. " >= " .. B .. ")"
            elseif Name == "JUMPIFNOTEQ" then
                return "(" .. A .. " == " .. B .. ")"
            elseif Name == "JUMPIFNOTLE" then
                return "(" .. A .. " <= " .. B .. ")"
            end
            return "(" .. A .. " < " .. B .. ")"
        elseif Name == "JUMPXEQKNIL" then
            local Equal = A .. " == nil"
            return (math.floor((Instruction.Aux or 0) / 2147483648) % 2 == 0) and ("(" .. A .. " ~= nil)") or ("(" .. Equal .. ")")
        elseif Name == "JUMPXEQKB" then
            local Constant = (Instruction.Aux or 0) % 2 == 1 and "true" or "false"
            local Equal = A .. " == " .. Constant
            return (math.floor((Instruction.Aux or 0) / 2147483648) % 2 == 0) and ("(" .. A .. " ~= " .. Constant .. ")") or ("(" .. Equal .. ")")
        elseif Name == "JUMPXEQKN" or Name == "JUMPXEQKS" then
            local ConstantIndex = (Instruction.Aux or 0) % 16777216
            local Constant = ConstantExpression(Proto, ConstantIndex, Strings)
            local Equal = A .. " == " .. Constant
            return (math.floor((Instruction.Aux or 0) / 2147483648) % 2 == 0) and ("(" .. A .. " ~= " .. Constant .. ")") or ("(" .. Equal .. ")")
        end
        return nil
    end
    local function IsConditionalJump(Name)
        return Name == "JUMPIF" or Name == "JUMPIFNOT" or Name == "JUMPIFEQ" or Name == "JUMPIFLE" or Name == "JUMPIFLT" or Name == "JUMPIFNOTEQ" or Name == "JUMPIFNOTLE" or Name == "JUMPIFNOTLT" or Name == "JUMPXEQKNIL" or Name == "JUMPXEQKB" or Name == "JUMPXEQKN" or Name == "JUMPXEQKS"
    end
    local WhileLoopStarts = {}
    local WhileLoopBranches = {}
    local WhileLoopBacks = {}
    local WhileLoopContinues = {}
    local RepeatLoopStarts = {}
    local RepeatLoopBranches = {}
    local ForLoopStarts = {}
    local ForLoopEnds = {}
    for InstructionIndex, Instruction in ipairs(Instructions) do
        local Name = Instruction.Name
        if IsConditionalJump(Name) then
            local TargetIndex = GetTargetIndex(Instruction)
            if TargetIndex <= InstructionIndex then
                if not RepeatLoopStarts[TargetIndex] then
                    RepeatLoopStarts[TargetIndex] = {BranchIndex = InstructionIndex, Condition = GetFallthroughCondition(Instruction)}
                    RepeatLoopBranches[InstructionIndex] = true
                end
            elseif TargetIndex > InstructionIndex + 1 then
                local BackEdges = {}
                local LoopStartIndex = nil
                for CandidateIndex = InstructionIndex + 1, math.min(TargetIndex - 1, #Instructions) do
                    local Candidate = Instructions[CandidateIndex]
                    if Candidate.Name == "JUMPBACK" or Candidate.Name == "JUMP" or Candidate.Name == "JUMPX" then
                        local BackTarget = GetTargetIndex(Candidate)
                        local IsOuterContinue = false
                        if BackTarget <= InstructionIndex then
                            for ExistingStart, ExistingLoop in pairs(WhileLoopStarts) do
                                if InstructionIndex > ExistingLoop.BranchIndex and InstructionIndex < ExistingLoop.EndIndex and BackTarget >= ExistingStart and BackTarget <= ExistingLoop.BranchIndex then
                                    IsOuterContinue = true
                                    break
                                end
                            end
                            if not IsOuterContinue then
                                LoopStartIndex = LoopStartIndex and math.min(LoopStartIndex, BackTarget) or BackTarget
                                BackEdges[#BackEdges + 1] = {Index = CandidateIndex, Target = BackTarget}
                            end
                        end
                    end
                end
                if LoopStartIndex then
                    local LoopBackEdges = {}
                    for _, BackEdge in ipairs(BackEdges) do
                        if BackEdge.Target == LoopStartIndex then
                            LoopBackEdges[#LoopBackEdges + 1] = BackEdge.Index
                        end
                    end
                    local BackIndex = LoopBackEdges[#LoopBackEdges]
                    WhileLoopStarts[LoopStartIndex] = {BranchIndex = InstructionIndex, BackIndex = BackIndex, EndIndex = TargetIndex, ExitCondition = "not (" .. GetFallthroughCondition(Instruction) .. ")"}
                    WhileLoopBranches[InstructionIndex] = true
                    WhileLoopBacks[BackIndex] = true
                    for _, BackEdge in ipairs(BackEdges) do
                        if BackEdge.Index ~= BackIndex then
                            WhileLoopContinues[BackEdge.Index] = true
                        end
                    end
                end
            end
        elseif Name == "FORNPREP" or Name == "FORGPREP" or Name == "FORGPREP_INEXT" or Name == "FORGPREP_NEXT" then
            local ExpectedLoopName = Name == "FORNPREP" and "FORNLOOP" or "FORGLOOP"
            local CandidateIndex = GetTargetIndex(Instruction)
            local Candidate = Instructions[CandidateIndex]
            if not Candidate or Candidate.Name ~= ExpectedLoopName or Candidate.A ~= Instruction.A or GetTargetIndex(Candidate) ~= InstructionIndex + 1 then
                CandidateIndex = nil
                for SearchIndex = InstructionIndex + 1, #Instructions do
                    local SearchCandidate = Instructions[SearchIndex]
                    if SearchCandidate.Name == ExpectedLoopName and SearchCandidate.A == Instruction.A and GetTargetIndex(SearchCandidate) == InstructionIndex + 1 then
                        CandidateIndex = SearchIndex
                        Candidate = SearchCandidate
                        break
                    end
                end
            end
            if CandidateIndex then
                if Name == "FORNPREP" then
                    ForLoopStarts[InstructionIndex] = {LoopIndex = CandidateIndex, Kind = "Numeric"}
                else
                    ForLoopStarts[InstructionIndex] = {LoopIndex = CandidateIndex, Kind = "Generic", VariableCount = (Candidate.Aux or 2) % 256}
                end
                ForLoopEnds[CandidateIndex] = true
            end
        end
    end
    local Blocks = {}
    local function CloseBlock(Block)
        if Block.Kind == "Repeat" then
            IndentLevel = math.max(0, IndentLevel - 1)
            EmitLine("until " .. (Block.Condition or "false"))
        else
            IndentLevel = math.max(0, IndentLevel - 1)
            EmitLine("end")
        end
    end
    local HasReturn = false
    local InstructionIndex = 1
    while InstructionIndex <= #Instructions do
        YieldControl()
        while #Blocks > 0 and InstructionIndex >= Blocks[#Blocks].EndIndex and Blocks[#Blocks].Kind ~= "Repeat" and not (Blocks[#Blocks].Kind == "For" and ForLoopEnds[InstructionIndex]) do
            local Block = table.remove(Blocks)
            CloseBlock(Block)
        end
        local ActiveInstruction = Instructions[InstructionIndex]
        ActiveInstructionIndex = InstructionIndex
        CurrentPC = ActiveInstruction.PC
        local RepeatStart = RepeatLoopStarts[InstructionIndex]
        if RepeatStart then
            EmitLine("repeat")
            IndentLevel = IndentLevel + 1
            Blocks[#Blocks + 1] = {Kind = "Repeat", EndIndex = RepeatStart.BranchIndex, Condition = RepeatStart.Condition}
        end
        local WhileStart = WhileLoopStarts[InstructionIndex]
        if WhileStart then
            EmitLine("while true do")
            IndentLevel = IndentLevel + 1
            Blocks[#Blocks + 1] = {Kind = "While", EndIndex = WhileStart.EndIndex}
        end
        if RepeatLoopBranches[InstructionIndex] then
            local RepeatBlock = Blocks[#Blocks]
            if not RepeatBlock or RepeatBlock.Kind ~= "Repeat" then
                return nil, "Repeat-loop structure could not be matched"
            end
            table.remove(Blocks)
            CloseBlock(RepeatBlock)
            InstructionIndex = InstructionIndex + 1
            continue
        end
        if WhileLoopBranches[InstructionIndex] then
            local Loop = nil
            for _, Candidate in pairs(WhileLoopStarts) do
                if Candidate.BranchIndex == InstructionIndex then
                    Loop = Candidate
                    break
                end
            end
            if not Loop then
                return nil, "While-loop branch could not be matched"
            end
            EmitLine("if " .. Loop.ExitCondition .. " then break end")
            InstructionIndex = InstructionIndex + 1
            continue
        end
        if WhileLoopBacks[InstructionIndex] then
            InstructionIndex = InstructionIndex + 1
            continue
        end
        if WhileLoopContinues[InstructionIndex] then
            EmitLine("continue")
            InstructionIndex = InstructionIndex + 1
            continue
        end
        if ForLoopEnds[InstructionIndex] then
            local ForBlockIndex = nil
            for BlockIndex = #Blocks, 1, -1 do
                local Block = Blocks[BlockIndex]
                if Block.Kind == "For" and Block.EndIndex == InstructionIndex then
                    ForBlockIndex = BlockIndex
                    break
                end
            end
            if not ForBlockIndex then
                return nil, "For-loop end at instruction " .. tostring(ActiveInstruction.PC) .. " has no matching loop start"
            end
            while #Blocks >= ForBlockIndex do
                CloseBlock(table.remove(Blocks))
            end
            InstructionIndex = InstructionIndex + 1
            continue
        end
        local ForLoop = ForLoopStarts[InstructionIndex]
        if ForLoop then
            local A = Instructions[InstructionIndex].A
            if ForLoop.Kind == "Numeric" then
                local VariableName = Registers[A + 3] or GetDebugLocalName(Proto, A + 3, Instructions[InstructionIndex].PC, UsedNames, UsePascalCase)
                local InitialValue = GetReg(A + 2)
                local LimitValue = GetReg(A)
                local StepValue = GetReg(A + 1)
                Registers[A + 3] = VariableName
                Declared[A + 3] = true
                InvalidateRegister(A)
                InvalidateRegister(A + 1)
                InvalidateRegister(A + 2)
                InvalidateRegister(A + 3, VariableName)
                EmitLine("for " .. VariableName .. " = " .. InitialValue .. ", " .. LimitValue .. ", " .. StepValue .. " do")
            else
                local VariableCount = ForLoop.VariableCount
                if VariableCount < 1 then
                    VariableCount = 2
                end
                local GeneratorExpression = GetReg(A)
                local StateExpression = GetReg(A + 1)
                local InitialExpression = GetReg(A + 2)
                local Variables = {}
                for Register = A + 3, A + 2 + VariableCount do
                    local VariableName = Registers[Register] or GetDebugLocalName(Proto, Register, Instructions[InstructionIndex].PC, UsedNames, UsePascalCase)
                    Registers[Register] = VariableName
                    Declared[Register] = true
                    InvalidateRegister(Register, VariableName)
                    Variables[#Variables + 1] = VariableName
                end
                InvalidateRegister(A)
                InvalidateRegister(A + 1)
                InvalidateRegister(A + 2)
                EmitLine("for " .. table.concat(Variables, ", ") .. " in " .. GeneratorExpression .. ", " .. StateExpression .. ", " .. InitialExpression .. " do")
            end
            IndentLevel = IndentLevel + 1
            Blocks[#Blocks + 1] = {Kind = "For", EndIndex = ForLoop.LoopIndex}
            InstructionIndex = InstructionIndex + 1
            continue
        end
        local Instruction = Instructions[InstructionIndex]
        local Name = Instruction.Name
        local A, B, C = Instruction.A, Instruction.B, Instruction.C
        local PC = Instruction.PC
        local Aux = Instruction.Aux
        if IsConditionalJump(Name) then
            local TargetIndex = GetTargetIndex(Instruction)
            local Condition = GetFallthroughCondition(Instruction)
            if not Condition then
                return nil, "Condition reconstruction is not available for " .. Name
            end
            if TargetIndex > InstructionIndex + 1 then
                EmitLine("if " .. Condition .. " then")
                IndentLevel = IndentLevel + 1
                Blocks[#Blocks + 1] = {Kind = "If", EndIndex = TargetIndex}
            elseif TargetIndex <= InstructionIndex then
                return nil, "Backward branch was not recognized as a structured loop"
            end
        elseif Name == "JUMP" or Name == "JUMPBACK" or Name == "JUMPX" then
            local TargetIndex = GetTargetIndex(Instruction)
            local TopBlock = Blocks[#Blocks]
            local LoopBlockIndex = nil
            local LoopAction = nil
            for BlockIndex = #Blocks, 1, -1 do
                local Block = Blocks[BlockIndex]
                if Block.Kind == "While" and TargetIndex == Block.EndIndex then
                    LoopBlockIndex = BlockIndex
                    LoopAction = "break"
                    break
                elseif Block.Kind == "For" and TargetIndex == Block.EndIndex + 1 then
                    LoopBlockIndex = BlockIndex
                    LoopAction = "break"
                    break
                elseif Block.Kind == "For" and TargetIndex == Block.EndIndex then
                    LoopBlockIndex = BlockIndex
                    LoopAction = "continue"
                    break
                end
            end
            if LoopBlockIndex then
                EmitLine(LoopAction)
            elseif Name == "JUMP" and TopBlock and TopBlock.Kind == "If" and InstructionIndex + 1 == TopBlock.EndIndex and TargetIndex > TopBlock.EndIndex then
                IndentLevel = math.max(0, IndentLevel - 1)
                EmitLine("else")
                IndentLevel = IndentLevel + 1
                TopBlock.EndIndex = TargetIndex
            elseif TopBlock and TopBlock.Kind == "If" and TargetIndex == TopBlock.EndIndex then
            elseif TargetIndex <= InstructionIndex then
                return nil, "Unmatched backward jump at instruction " .. tostring(Instruction.PC)
            elseif TargetIndex > InstructionIndex + 1 then
                return nil, "Unmatched forward jump at instruction " .. tostring(Instruction.PC)
            end
        elseif Name == "CMPPROTO" then
            return nil, "CMPPROTO class dispatch requires advanced reconstruction"
        elseif Name == "NOP" or Name == "BREAK" or Name == "CLOSEUPVALS" or Name == "PREPVARARGS" or Name == "COVERAGE" or Name == "NATIVECALL" or Name == "FASTCALL" or Name == "FASTCALL1" or Name == "FASTCALL2" or Name == "FASTCALL2K" or Name == "FASTCALL3" or Name == "FASTPCALL" then
        elseif Name == "LOADNIL" then
            WriteReg(A, "nil", PC, nil, true, nil, true)
        elseif Name == "LOADB" then
            WriteReg(A, B ~= 0 and "true" or "false", PC, B ~= 0, true, nil, true)
            if C ~= 0 then
                local TargetPc = PC + C + 1
                local TargetIndex = InstructionIndexByPc[TargetPc]
                if not TargetIndex then
                    return nil, "LOADB skip target is invalid"
                end
                InstructionIndex = TargetIndex
                if #Lines > MaxOutputLines then
                    return nil, "Reconstructed source exceeds the output safety limit"
                end
                continue
            end
        elseif Name == "LOADN" then
            WriteReg(A, tostring(Instruction.D), PC, Instruction.D, true, nil, true)
        elseif Name == "LOADK" then
            local Constant = GetConstant(Proto, Instruction.D)
            local KnownValue, IsKnown = GetConstantKnown(Constant)
            WriteReg(A, ConstantExpression(Proto, Instruction.D, Strings), PC, KnownValue, IsKnown, nil, true)
        elseif Name == "LOADKX" then
            local Constant = GetConstant(Proto, Aux)
            local KnownValue, IsKnown = GetConstantKnown(Constant)
            WriteReg(A, ConstantExpression(Proto, Aux, Strings), PC, KnownValue, IsKnown, nil, true)
        elseif Name == "MOVE" then
            WriteReg(A, GetReg(B), PC, KnownValues[B], KnownValueFlags[B], GetRegExpression(B), true)
        elseif Name == "GETGLOBAL" then
            local Key = GetConstant(Proto, Aux % 16777216)
            if Key.Kind ~= "String" then
                return nil, "GETGLOBAL does not reference a string constant"
            end
            local Expression = IsIdentifier(Key.Value) and Key.Value or "_G[" .. Quote(Key.Value) .. "]"
            WriteReg(A, Expression, PC, nil, false, Expression, true)
        elseif Name == "SETGLOBAL" then
            local Key = GetConstant(Proto, Aux % 16777216)
            if Key.Kind ~= "String" then
                return nil, "SETGLOBAL does not reference a string constant"
            end
            local Expression = IsIdentifier(Key.Value) and Key.Value or "_G[" .. Quote(Key.Value) .. "]"
            EmitLine(Expression .. " = " .. GetReg(A))
        elseif Name == "GETUPVAL" then
            local UpvalueName = CaptureNames[B + 1] or Proto.DebugUpvalues[B + 1] or ("Upvalue" .. tostring(B + 1))
            if UsePascalCase and not CaptureNames[B + 1] then
                UpvalueName = PascalCase(UpvalueName)
            end
            WriteReg(A, UpvalueName, PC, nil, false, UpvalueName, true)
        elseif Name == "SETUPVAL" then
            local UpvalueName = CaptureNames[B + 1] or Proto.DebugUpvalues[B + 1] or ("Upvalue" .. tostring(B + 1))
            if UsePascalCase and not CaptureNames[B + 1] then
                UpvalueName = PascalCase(UpvalueName)
            end
            EmitLine(UpvalueName .. " = " .. GetReg(A))
        elseif Name == "GETTABLEKS" or Name == "GETUDATAKS" then
            local ConstantIndex = Name == "GETUDATAKS" and (Aux % 65536) or Aux
            local Key = GetConstant(Proto, ConstantIndex)
            if Key.Kind ~= "String" then
                return nil, Name .. " does not reference a string constant"
            end
            local Expression = GetProperty(GetReg(B), Key.Value)
            local ExpressionValue = GetProperty(GetRegExpression(B), Key.Value)
            WriteReg(A, Expression, PC, nil, false, ExpressionValue, true)
        elseif Name == "GETTABLE" then
            WriteReg(A, GetReg(B) .. "[" .. GetReg(C) .. "]", PC, nil, false, nil, true)
        elseif Name == "GETTABLEN" then
            WriteReg(A, GetReg(B) .. "[" .. tostring(C + 1) .. "]", PC, nil, false, nil, true)
        elseif Name == "SETTABLEKS" or Name == "SETUDATAKS" then
            local ConstantIndex = Name == "SETUDATAKS" and (Aux % 65536) or Aux
            local Key = GetConstant(Proto, ConstantIndex)
            if Key.Kind ~= "String" then
                return nil, Name .. " does not reference a string constant"
            end
            EmitLine(GetProperty(GetReg(B), Key.Value) .. " = " .. GetReg(A))
        elseif Name == "SETTABLE" then
            EmitLine(GetReg(B) .. "[" .. GetReg(C) .. "] = " .. GetReg(A))
        elseif Name == "SETTABLEN" then
            EmitLine(GetReg(B) .. "[" .. tostring(C + 1) .. "] = " .. GetReg(A))
        elseif Name == "ADD" or Name == "SUB" or Name == "MUL" or Name == "DIV" or Name == "MOD" or Name == "POW" or Name == "IDIV" or Name == "AND" or Name == "OR" then
            local Operators = {ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//", AND = "and", OR = "or"}
            local IsKnown = KnownValueFlags[B] and KnownValueFlags[C]
            local Folded, FoldedValue = false, nil
            if IsKnown then
                Folded, FoldedValue = TryFoldBinary(Name, KnownValues[B], KnownValues[C])
            end
            local Expression = Folded and FormatKnownValue(FoldedValue) or ("(" .. GetReg(B) .. " " .. Operators[Name] .. " " .. GetReg(C) .. ")")
            WriteReg(A, Expression, PC, FoldedValue, Folded, nil, true)
        elseif Name == "ADDK" or Name == "SUBK" or Name == "MULK" or Name == "DIVK" or Name == "MODK" or Name == "POWK" or Name == "IDIVK" or Name == "ANDK" or Name == "ORK" then
            local Operators = {ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//", ANDK = "and", ORK = "or"}
            local Constant = GetConstant(Proto, C)
            local ConstantValue, ConstantKnown = GetConstantKnown(Constant)
            local Folded, FoldedValue = false, nil
            if KnownValueFlags[B] and ConstantKnown then
                local BaseName = Name:gsub("K$", "")
                Folded, FoldedValue = TryFoldBinary(BaseName, KnownValues[B], ConstantValue)
            end
            local Expression = Folded and FormatKnownValue(FoldedValue) or ("(" .. GetReg(B) .. " " .. Operators[Name] .. " " .. ConstantExpression(Proto, C, Strings) .. ")")
            WriteReg(A, Expression, PC, FoldedValue, Folded, nil, true)
        elseif Name == "SUBRK" or Name == "DIVRK" then
            local Operator = Name == "SUBRK" and "-" or "/"
            local Constant = GetConstant(Proto, B)
            local ConstantValue, ConstantKnown = GetConstantKnown(Constant)
            local Folded, FoldedValue = false, nil
            if ConstantKnown and KnownValueFlags[C] then
                Folded, FoldedValue = TryFoldBinary(Name == "SUBRK" and "SUB" or "DIV", ConstantValue, KnownValues[C])
            end
            local Expression = Folded and FormatKnownValue(FoldedValue) or ("(" .. ConstantExpression(Proto, B, Strings) .. " " .. Operator .. " " .. GetReg(C) .. ")")
            WriteReg(A, Expression, PC, FoldedValue, Folded, nil, true)
        elseif Name == "NOT" then
            local IsKnown = KnownValueFlags[B] == true
            local Value = false
            if IsKnown then
                Value = not KnownValues[B]
            end
            WriteReg(A, IsKnown and (Value and "true" or "false") or ("(not " .. GetReg(B) .. ")"), PC, Value, IsKnown, nil, true)
        elseif Name == "MINUS" then
            local IsKnown = KnownValueFlags[B] and type(KnownValues[B]) == "number"
            local Value = IsKnown and -KnownValues[B] or nil
            WriteReg(A, IsKnown and FormatKnownValue(Value) or ("(-" .. GetReg(B) .. ")"), PC, Value, IsKnown and FormatKnownValue(Value) ~= nil, nil, true)
        elseif Name == "LENGTH" then
            local IsKnown = KnownValueFlags[B] and type(KnownValues[B]) == "string"
            local Value = IsKnown and #KnownValues[B] or nil
            WriteReg(A, IsKnown and tostring(Value) or ("(#" .. GetReg(B) .. ")"), PC, Value, IsKnown, nil, true)
        elseif Name == "CONCAT" then
            local Parts = {}
            local Values = {}
            local AllKnown = true
            for Register = B, C do
                Parts[#Parts + 1] = GetReg(Register)
                if KnownValueFlags[Register] and (type(KnownValues[Register]) == "string" or type(KnownValues[Register]) == "number") then
                    Values[#Values + 1] = tostring(KnownValues[Register])
                else
                    AllKnown = false
                end
            end
            local FoldedValue = AllKnown and table.concat(Values) or nil
            WriteReg(A, AllKnown and Quote(FoldedValue) or ("(" .. table.concat(Parts, " .. ") .. ")"), PC, FoldedValue, AllKnown, nil, true)
        elseif Name == "NEWTABLE" then
            WriteReg(A, "{}", PC)
        elseif Name == "DUPTABLE" then
            WriteReg(A, ConstantExpression(Proto, Instruction.D, Strings), PC)
        elseif Name == "GETIMPORT" then
            local Import = Aux or 0
            local Length = math.floor(Import / 1073741824) % 4
            if Length < 1 or Length > 3 then
                return nil, "GETIMPORT contains an invalid import path"
            end
            local ImportIndices = {math.floor(Import / 1048576) % 1024, math.floor(Import / 1024) % 1024, Import % 1024}
            local ImportParts = {}
            for ImportIndex = 1, Length do
                local ImportConstant = GetConstant(Proto, ImportIndices[ImportIndex])
                if ImportConstant.Kind ~= "String" then
                    return nil, "GETIMPORT path references a non-string constant"
                end
                local ImportPart = ImportConstant.Value
                if IsIdentifier(ImportPart) then
                    ImportParts[#ImportParts + 1] = ImportPart
                elseif ImportIndex == 1 then
                    ImportParts[#ImportParts + 1] = "_G[" .. Quote(ImportPart) .. "]"
                else
                    ImportParts[#ImportParts + 1] = "[" .. Quote(ImportPart) .. "]"
                end
            end
            local Expression = ImportParts[1]
            for ImportIndex = 2, #ImportParts do
                if ImportParts[ImportIndex]:sub(1, 1) == "[" then
                    Expression = Expression .. ImportParts[ImportIndex]
                else
                    Expression = Expression .. "." .. ImportParts[ImportIndex]
                end
            end
            WriteReg(A, Expression, PC, nil, false, Expression, true)
        elseif Name == "NAMECALL" or Name == "NAMECALLUDATA" then
            local ConstantIndex = Name == "NAMECALLUDATA" and (Aux % 65536) or Aux
            local MethodConstant = GetConstant(Proto, ConstantIndex)
            if MethodConstant.Kind ~= "String" then
                return nil, Name .. " does not reference a string method name"
            end
            NameCalls[A] = {Receiver = GetReg(B), Method = MethodConstant.Value}
            InvalidateRegister(A)
            InvalidateRegister(A + 1)
        elseif Name == "CALL" or Name == "CALLFB" then
            local MethodCall = NameCalls[A]
            local FirstArgument = A + (MethodCall and 2 or 1)
            local Arguments = {}
            local KnownArguments = {}
            local AllArgumentsKnown = true
            local function AddArgument(Register)
                local ArgumentIndex = #Arguments + 1
                Arguments[ArgumentIndex] = GetReg(Register)
                if KnownValueFlags[Register] then
                    KnownArguments[ArgumentIndex] = KnownValues[Register]
                else
                    AllArgumentsKnown = false
                end
            end
            if B == 0 then
                if MultiValue and MultiValueStart and MultiValueStart >= FirstArgument then
                    for Register = FirstArgument, MultiValueStart - 1 do
                        AddArgument(Register)
                    end
                    Arguments[#Arguments + 1] = MultiValue
                    AllArgumentsKnown = false
                    MultiValue = nil
                    MultiValueStart = nil
                elseif HighestRegister >= FirstArgument then
                    for Register = FirstArgument, HighestRegister do
                        AddArgument(Register)
                    end
                else
                    return nil, "Variable-argument CALL has no recoverable argument range"
                end
            else
                for Register = FirstArgument, A + B - 1 do
                    AddArgument(Register)
                end
            end
            local Call
            local FunctionExpression = MethodCall and (MethodCall.Receiver .. "." .. MethodCall.Method) or GetRegExpression(A)
            if MethodCall then
                if IsIdentifier(MethodCall.Method) then
                    Call = MethodCall.Receiver .. ":" .. MethodCall.Method .. "(" .. table.concat(Arguments, ", ") .. ")"
                else
                    local ExplicitArguments = {MethodCall.Receiver}
                    for _, Argument in ipairs(Arguments) do
                        ExplicitArguments[#ExplicitArguments + 1] = Argument
                    end
                    Call = GetProperty(MethodCall.Receiver, MethodCall.Method) .. "(" .. table.concat(ExplicitArguments, ", ") .. ")"
                end
                NameCalls[A] = nil
            else
                local FunctionValue = GetReg(A)
                if type(FunctionExpression) == "string" and IsIdentifier(FunctionExpression) then
                    FunctionValue = FunctionExpression
                end
                Call = FunctionValue .. "(" .. table.concat(Arguments, ", ") .. ")"
            end
            local ResultCount = C - 1
            if C == 0 then
                MultiValue = Call
                MultiValueStart = A
                HighestRegister = math.max(HighestRegister, A)
                InvalidateRegister(A)
            elseif ResultCount == 0 then
                EmitLine(Call)
                MultiValue = nil
                MultiValueStart = nil
            elseif ResultCount == 1 then
                local FoldSuccess, FoldedValue = false, nil
                if AllArgumentsKnown then
                    FoldSuccess, FoldedValue = TryFoldCall(FunctionExpression, KnownArguments, #Arguments)
                end
                local FoldedExpression = FoldSuccess and FormatKnownValue(FoldedValue) or Call
                local NamingExpression
                if MethodCall and type(KnownArguments[1]) == "string" then
                    local MethodName = MethodCall.Method
                    if MethodName == "GetService" or MethodName == "WaitForChild" or MethodName == "FindFirstChild" or MethodName == "FindFirstAncestor" then
                        NamingExpression = MethodCall.Receiver .. ":" .. MethodName .. "(" .. Quote(KnownArguments[1]) .. ")"
                    end
                end
                WriteReg(A, FoldedExpression, PC, FoldedValue, FoldSuccess, NamingExpression)
                MultiValue = nil
                MultiValueStart = nil
            elseif ResultCount <= 16 then
                local ResultNames = {}
                local ResultWasDeclared = {}
                local FunctionLookup = type(FunctionExpression) == "string" and string.lower(FunctionExpression) or ""
                local IsProtectedCall = not MethodCall and (FunctionLookup == "pcall" or FunctionLookup == "xpcall")
                for Offset = 0, ResultCount - 1 do
                    local Register = A + Offset
                    local BaseName
                    if IsProtectedCall and Offset == 0 then
                        BaseName = "Success"
                    elseif IsProtectedCall and Offset == 1 then
                        BaseName = "Result"
                    elseif FunctionExpression == "string.gsub" and Offset == 1 then
                        BaseName = "ReplacementCount"
                    elseif FunctionExpression == "string.find" and Offset == 0 then
                        BaseName = "StartIndex"
                    elseif FunctionExpression == "string.find" and Offset == 1 then
                        BaseName = "EndIndex"
                    else
                        BaseName = Offset == 0 and "Result" or ("Result" .. tostring(Offset + 1))
                    end
                    RefreshRegisterLocal(Register, PC)
                    local ActiveLocal = GetActiveDebugLocal(Register, PC)
                    if not ActiveLocal and Register >= Proto.NumParams then
                        Registers[Register] = GetFreshRegisterName(BaseName)
                        RegisterExpressions[Register] = Registers[Register]
                        RegisterInline[Register] = false
                        KnownValues[Register] = nil
                        KnownValueFlags[Register] = false
                        RegisterWritten[Register] = false
                        Declared[Register] = false
                    elseif ActiveLocal and Register >= Proto.NumParams and IsGenericDebugName(ActiveLocal.Name) then
                        local ExistingBase = PascalCase(ActiveLocal.Name)
                        if ExistingBase ~= BaseName then
                            Registers[Register] = GetFreshRegisterName(BaseName)
                            RegisterExpressions[Register] = Registers[Register]
                            DebugLocalNames[ActiveLocal] = Registers[Register]
                            RegisterInline[Register] = false
                            KnownValues[Register] = nil
                            KnownValueFlags[Register] = false
                            RegisterWritten[Register] = false
                            Declared[Register] = false
                        end
                    end
                    local WasDeclared = Declared[Register] == true
                    local ResultName = DeclareRegister(Register, PC, IndentLevel == 0)
                    RegisterWritten[Register] = true
                    RegisterInline[Register] = false
                    RegisterExpressions[Register] = ResultName
                    HighestRegister = math.max(HighestRegister, Register)
                    ResultNames[#ResultNames + 1] = ResultName
                    ResultWasDeclared[#ResultWasDeclared + 1] = WasDeclared
                end
                local CanDeclareAllLocally = IndentLevel == 0
                for _, WasDeclared in ipairs(ResultWasDeclared) do
                    if WasDeclared then
                        CanDeclareAllLocally = false
                    end
                end
                if CanDeclareAllLocally then
                    EmitLine("local " .. table.concat(ResultNames, ", ") .. " = " .. Call)
                else
                    for Index, WasDeclared in ipairs(ResultWasDeclared) do
                        if not WasDeclared and IndentLevel == 0 and not TopDeclarationSet[ResultNames[Index]] then
                            TopDeclarationSet[ResultNames[Index]] = true
                            TopDeclarations[#TopDeclarations + 1] = ResultNames[Index]
                        end
                    end
                    EmitLine(table.concat(ResultNames, ", ") .. " = " .. Call)
                end
                MultiValue = nil
                MultiValueStart = nil
            else
                return nil, "CALL produces more than sixteen results"
            end
        elseif Name == "RETURN" then
            HasReturn = true
            local Values = {}
            if B == 0 then
                if MultiValue and MultiValueStart and MultiValueStart >= A then
                    for Register = A, MultiValueStart - 1 do
                        Values[#Values + 1] = GetReg(Register)
                    end
                    Values[#Values + 1] = MultiValue
                    MultiValue = nil
                    MultiValueStart = nil
                else
                    for Register = A, HighestRegister do
                        Values[#Values + 1] = GetReg(Register)
                    end
                end
            else
                for Register = A, A + B - 2 do
                    Values[#Values + 1] = GetReg(Register)
                end
            end
            if #Values == 0 then
                EmitLine("return")
            else
                EmitLine("return " .. table.concat(Values, ", "))
            end
        elseif Name == "GETVARARGS" then
            if B == 0 then
                MultiValue = "..."
                MultiValueStart = A
                HighestRegister = math.max(HighestRegister, A)
                InvalidateRegister(A)
            else
                if B <= 1 then
                    return nil, "GETVARARGS has an invalid fixed result count"
                end
            local VarargNames = {}
            for Register = A, A + B - 2 do
                local VarargName = DeclareRegister(Register, PC)
                VarargNames[#VarargNames + 1] = VarargName
                HighestRegister = math.max(HighestRegister, Register)
                InvalidateRegister(Register, VarargName)
            end
            EmitLine(table.concat(VarargNames, ", ") .. " = ...")
            end
        elseif Name == "NEWCLOSURE" or Name == "DUPCLOSURE" then
            if not Parsed then
                return nil, "Prototype metadata is unavailable for nested function reconstruction"
            end
            local ChildProtoIndex
            if Name == "NEWCLOSURE" then
                ChildProtoIndex = Proto.Children[Instruction.D + 1]
            else
                local ClosureConstant = GetConstant(Proto, Instruction.D)
                if ClosureConstant.Kind ~= "Closure" then
                    return nil, "DUPCLOSURE does not reference a closure constant"
                end
                ChildProtoIndex = ClosureConstant.Value
            end
            local ChildProto = ChildProtoIndex and Parsed.Protos[ChildProtoIndex + 1]
            if not ChildProto then
                return nil, "Nested prototype index is invalid"
            end
            local ChildCaptureNames = {}
            local CaptureCount = ChildProto.NumUpvalues
            for CaptureIndex = 1, CaptureCount do
                local CaptureInstruction = Instructions[InstructionIndex + CaptureIndex]
                if not CaptureInstruction or CaptureInstruction.Name ~= "CAPTURE" then
                    return nil, "Nested closure capture sequence is incomplete"
                end
                if CaptureInstruction.A == 0 or CaptureInstruction.A == 1 then
                    ChildCaptureNames[CaptureIndex] = GetReg(CaptureInstruction.B)
                elseif CaptureInstruction.A == 2 then
                    ChildCaptureNames[CaptureIndex] = CaptureNames[CaptureInstruction.B + 1] or Proto.DebugUpvalues[CaptureInstruction.B + 1] or ("Upvalue" .. tostring(CaptureInstruction.B + 1))
                else
                    return nil, "Unknown closure capture mode " .. tostring(CaptureInstruction.A)
                end
            end
            local ChildParams = {}
            local ChildUsedNames = {}
            for _, CaptureName in pairs(ChildCaptureNames) do
                ChildUsedNames[CaptureName] = true
            end
            for Register = 0, ChildProto.NumParams - 1 do
                ChildParams[#ChildParams + 1] = GetDebugLocalName(ChildProto, Register, 0, ChildUsedNames, UsePascalCase)
            end
            local ChildBody, ChildError = ReconstructLinear(ChildProto, Strings, Options, Parsed, ChildCaptureNames, CurrentDepth + 1)
            if not ChildBody then
                return nil, "Nested function reconstruction failed: " .. tostring(ChildError)
            end
            local FunctionLines = {}
            for BodyLine in (ChildBody .. "\n"):gmatch("(.-)\n") do
                FunctionLines[#FunctionLines + 1] = "    " .. BodyLine
            end
            local FunctionExpression = "function(" .. table.concat(ChildParams, ", ") .. ")\n" .. table.concat(FunctionLines, "\n") .. (ChildBody ~= "" and "\n" or "") .. "end"
            RefreshRegisterLocal(A, PC)
            local ChildDebugName = type(ChildProto.DebugName) == "string" and ChildProto.DebugName or ""
            local ActiveFunctionLocal = GetActiveDebugLocal(A, PC)
            if ChildDebugName ~= "" and #ChildDebugName >= 3 and not IsGenericDebugName(ChildDebugName) and not RegisterWritten[A] and not Declared[A] and (not ActiveFunctionLocal or IsGenericDebugName(ActiveFunctionLocal.Name)) then
                local FunctionName = GetFreshRegisterName(ChildDebugName)
                Registers[A] = FunctionName
                RegisterExpressions[A] = FunctionName
                RegisterInline[A] = false
                if ActiveFunctionLocal then
                    DebugLocalNames[ActiveFunctionLocal] = FunctionName
                end
            end
            WriteReg(A, FunctionExpression, PC)
            InstructionIndex = InstructionIndex + CaptureCount
        elseif Name == "CAPTURE" then
            return nil, "Unexpected CAPTURE instruction outside a closure"
        elseif Name == "SETLIST" then
            local StartIndex = (Aux or 0) + 1
            if C == 0 then
                local Values = {}
                if MultiValue and MultiValueStart and MultiValueStart >= B then
                    for Register = B, MultiValueStart - 1 do
                        Values[#Values + 1] = GetReg(Register)
                    end
                    Values[#Values + 1] = MultiValue
                else
                    for Register = B, HighestRegister do
                        Values[#Values + 1] = GetReg(Register)
                    end
                end
                if #Values > 0 then
                    local ValuesName = GetUniqueName("TableValues")
                    local IndexName = GetUniqueName("TableIndex")
                    local ValueName = GetUniqueName("TableValue")
                    EmitLine("local " .. ValuesName .. " = table.pack(" .. table.concat(Values, ", ") .. ")")
                    EmitLine("for " .. IndexName .. " = 1, " .. ValuesName .. ".n do")
                    IndentLevel = IndentLevel + 1
                    EmitLine(GetReg(A) .. "[" .. tostring(StartIndex) .. " + " .. IndexName .. " - 1] = " .. ValuesName .. "[" .. IndexName .. "]")
                    IndentLevel = math.max(0, IndentLevel - 1)
                    EmitLine("end")
                end
                MultiValue = nil
                MultiValueStart = nil
            else
                local Count = C - 1
                for Offset = 0, Count - 1 do
                    EmitLine(GetReg(A) .. "[" .. tostring(StartIndex + Offset) .. "] = " .. GetReg(B + Offset))
                end
            end
        elseif Name == "NEWCLASS" or Name == "CONSTRUCT" or Name == "FINCONSTRUCT" or Name == "NEWCLASSMEMBER" or Name == "GETPRIVATEFIELD" or Name == "SETPRIVATEFIELD" then
            return nil, "Advanced opcode " .. Name .. " requires fallback reconstruction"
        else
            return nil, "Native reconstruction does not yet support " .. Name
        end
        if #Lines > MaxOutputLines then
            return nil, "Reconstructed source exceeds the output safety limit"
        end
        InstructionIndex = InstructionIndex + 1
    end
    while #Blocks > 0 do
        local Block = table.remove(Blocks)
        if Block.Kind == "Repeat" then
            return nil, "Repeat-loop did not reach its matching condition"
        end
        CloseBlock(Block)
    end
    if #TopDeclarations + Proto.NumParams > 190 then
        return nil, "Function uses too many simultaneously live local registers for safe source reconstruction"
    end
    local OutputLines = {}
    if #TopDeclarations > 0 then
        for StartIndex = 1, #TopDeclarations, 100 do
            local DeclarationGroup = {}
            for Index = StartIndex, math.min(StartIndex + 99, #TopDeclarations) do
                DeclarationGroup[#DeclarationGroup + 1] = TopDeclarations[Index]
            end
            OutputLines[#OutputLines + 1] = "local " .. table.concat(DeclarationGroup, ", ")
        end
        if #Lines > 0 then
            OutputLines[#OutputLines + 1] = ""
        end
    end
    for _, Line in ipairs(Lines) do
        OutputLines[#OutputLines + 1] = Line
    end
    if not HasReturn and #OutputLines == 0 then
        return ""
    end
    return OptimizeTemporaryAssignments(table.concat(OutputLines, "\n"))
end
local function DisassembleParsed(Parsed, SelectedProto)
    local Lines = {
        "Valm Decompiler Disassembly",
        "Bytecode Version: " .. tostring(Parsed.Version),
        "Type Version: " .. tostring(Parsed.TypeVersion),
        "Prototype Count: " .. tostring(#Parsed.Protos),
        "Instruction Count: " .. tostring(Parsed.TotalInstructions),
        "Opcode Multiplier: " .. tostring(Parsed.OpcodeMultiplier or 1),
        ""
    }
    local Protos = SelectedProto and {SelectedProto} or Parsed.Protos
    for _, Proto in ipairs(Protos) do
        Lines[#Lines + 1] = "Function " .. tostring(Proto.Index) .. " " .. tostring(Proto.DebugName or "") .. ""
        Lines[#Lines + 1] = "Stack=" .. tostring(Proto.MaxStackSize) .. " Params=" .. tostring(Proto.NumParams) .. " Upvalues=" .. tostring(Proto.NumUpvalues)
        for _, Instruction in ipairs(Proto.Instructions) do
            local Line = string.format("%05d  %-18s A=%3d B=%3d C=%3d D=%6d", Instruction.PC, Instruction.Name, Instruction.A, Instruction.B, Instruction.C, Instruction.D)
            if Instruction.Aux then
                Line = Line .. string.format(" AUX=0x%08X", Instruction.Aux)
            end
            Lines[#Lines + 1] = Line
            if #Lines >= MaxOutputLines then
                Lines[#Lines + 1] = "Output truncated at the configured safety limit."
                return table.concat(Lines, "\n")
            end
        end
        Lines[#Lines + 1] = ""
    end
    return table.concat(Lines, "\n")
end
local function GetBytecode(Source)
    if type(Source) == "string" then
        return Source
    end
    local Provider = ActiveBytecodeProvider or GetScriptBytecode
    if type(Provider) ~= "function" then
        error("This executor does not expose getscriptbytecode or dumpstring", 0)
    end
    local Success, Result = pcall(Provider, Source)
    if not Success then
        error("Bytecode capture failed: " .. tostring(Result), 0)
    end
    if type(Result) ~= "string" then
        error("The executor returned no bytecode for this script", 0)
    end
    return Result
end
local function FindBytefall()
    local Candidates = {}
    local function AddCandidate(Candidate)
        if Candidate ~= nil then
            Candidates[#Candidates + 1] = Candidate
        end
    end
    AddCandidate(Env.Bytefall)
    AddCandidate(Env.ByteFall)
    AddCandidate(Env.bytefall)
    AddCandidate(Env.BytefallDecompiler)
    AddCandidate(Env.ByteFallDecompiler)
    AddCandidate(Env.BytefallDecompile)
    AddCandidate(Env.ByteFallDecompile)
    AddCandidate(Env.byteFallDecompile)
    AddCandidate(Env.bytefallDecompile)
    AddCandidate(Env.bytefall_decompile)
    AddCandidate(Env.Bytefall_Decompile)
    AddCandidate(Env.BytefallFallback)
    AddCandidate(Env.ByteFallFallback)
    AddCandidate(Env.bytefallFallback)
    AddCandidate(Env.BytefallAPI)
    AddCandidate(_G.Bytefall)
    AddCandidate(_G.ByteFall)
    AddCandidate(_G.bytefall)
    AddCandidate(_G.BytefallDecompiler)
    AddCandidate(_G.BytefallDecompile)
    AddCandidate(_G.ByteFallDecompiler)
    AddCandidate(_G.byteFallDecompile)
    AddCandidate(_G.bytefallDecompile)
    for _, Candidate in ipairs(Candidates) do
        if type(Candidate) == "function" then
            return Candidate
        elseif type(Candidate) == "table" then
            for _, Key in ipairs({"Decompile", "decompile", "DecompileScript", "decompileScript"}) do
                local Callback = Candidate[Key]
                if type(Callback) == "function" then
                    local LocalCallback = Callback
                    return function(Target, Bytecode, Options)
                        return LocalCallback(Target, Bytecode, Options)
                    end
                end
            end
        end
    end
    return nil
end
local ValmDecompiler = {
    Name = "Valm Decompiler",
    Version = "0.3.0-beta.29",
    BytecodeVersionMin = BytecodeVersionMin,
    BytecodeVersionMax = BytecodeVersionMax,
    BytefallFallback = nil,
    LastError = nil,
    FormatIdentifier = PascalCase,
    OpcodeNames = OpcodeNames,
    CacheLimit = CacheLimit,
    MaximumBytecodeBytes = MaxBytecodeBytes,
    MaximumInstructions = MaxInstructions,
    Cache = Cache,
    LastOpcodeMultiplier = nil
}
function ValmDecompiler.SetBytefallFallback(Callback)
    if Callback ~= nil and type(Callback) ~= "function" then
        error("Bytefall fallback must be a function or nil", 2)
    end
    ValmDecompiler.BytefallFallback = Callback
end
function ValmDecompiler.SetBytecodeProvider(Callback)
    if Callback ~= nil and type(Callback) ~= "function" then
        error("Bytecode provider must be a function or nil", 2)
    end
    ActiveBytecodeProvider = Callback or GetScriptBytecode
end
function ValmDecompiler.GetBytefallFallback()
    return ValmDecompiler.BytefallFallback or FindBytefall()
end
function ValmDecompiler.Parse(Source)
    local Bytecode = GetBytecode(Source)
    YieldCounter = 0
    local Parsed = ParseBytecode(Bytecode)
    ValmDecompiler.LastOpcodeMultiplier = Parsed.OpcodeMultiplier or 1
    return Parsed
end
function ValmDecompiler.Inspect(Source)
    local Success, Result = pcall(function()
        local Parsed = ValmDecompiler.Parse(Source)
        local PrototypeSummaries = {}
        for _, Proto in ipairs(Parsed.Protos) do
            PrototypeSummaries[#PrototypeSummaries + 1] = {
                Index = Proto.Index,
                Name = Proto.DebugName,
                InstructionCount = #Proto.Instructions,
                ConstantCount = #Proto.Constants,
                ChildCount = #Proto.Children,
                ParameterCount = Proto.NumParams,
                UpvalueCount = Proto.NumUpvalues
            }
        end
        return {
            BytecodeVersion = Parsed.Version,
            TypeVersion = Parsed.TypeVersion,
            PrototypeCount = #Parsed.Protos,
            InstructionCount = Parsed.TotalInstructions,
            MainPrototype = Parsed.MainProtoIndex,
            Prototypes = PrototypeSummaries
        }
    end)
    if not Success then
        ValmDecompiler.LastError = tostring(Result)
        return nil, ValmDecompiler.LastError
    end
    ValmDecompiler.LastError = nil
    return Result
end
function ValmDecompiler.Disassemble(Source, ProtoIndex)
    local Success, Result = pcall(function()
        local Parsed = ValmDecompiler.Parse(Source)
        local SelectedProto
        if ProtoIndex ~= nil then
            if type(ProtoIndex) ~= "number" or ProtoIndex < 0 or ProtoIndex % 1 ~= 0 then
                error("Prototype index must be a non-negative integer", 0)
            end
            SelectedProto = Parsed.Protos[ProtoIndex + 1]
            if not SelectedProto then
                error("Prototype index is outside the parsed chunk", 0)
            end
        end
        return DisassembleParsed(Parsed, SelectedProto)
    end)
    if not Success then
        ValmDecompiler.LastError = tostring(Result)
        return nil, ValmDecompiler.LastError
    end
    ValmDecompiler.LastError = nil
    return Result
end
function ValmDecompiler.Decompile(Source, Options)
    if type(Options) ~= "table" then
        Options = nil
    end
    local Bytecode
    local Success, CaptureResult = pcall(GetBytecode, Source)
    if not Success then
        ValmDecompiler.LastError = tostring(CaptureResult)
        return nil, ValmDecompiler.LastError
    end
    Bytecode = CaptureResult
    local IsSourceInstance = type(typeof) == "function" and typeof(Source) == "Instance"
    if IsSourceInstance then
        local Cached = Cache[Source]
        if Cached and Cached.Bytecode == Bytecode and Cached.OptionsKey == tostring(Options and Options.PascalCase ~= false) then
            return Cached.Source
        end
    end
    local Parsed
    local NativeSource
    local NativeError
    local NativeSuccess, NativeResult, NativeMessage = pcall(function()
        Parsed = ParseBytecode(Bytecode)
        ValmDecompiler.LastOpcodeMultiplier = Parsed.OpcodeMultiplier or 1
        return ReconstructLinear(Parsed.MainProto, Parsed.Strings, Options, Parsed, {}, 0)
    end)
    if NativeSuccess and type(NativeResult) == "string" then
        NativeSource = NativeResult
    elseif NativeSuccess then
        NativeError = NativeMessage or "Native reconstruction could not recover this script"
    else
        NativeError = tostring(NativeResult)
    end
    if NativeSource then
        if IsSourceInstance then
            Cache[Source] = {Bytecode = Bytecode, OptionsKey = tostring(Options and Options.PascalCase ~= false), Source = NativeSource}
            CacheOrder[#CacheOrder + 1] = Source
            if #CacheOrder > CacheLimit then
                local Removed = table.remove(CacheOrder, 1)
                Cache[Removed] = nil
            end
        end
        ValmDecompiler.LastError = nil
        return NativeSource
    end
    local Fallback
    local BytefallStatus
    if Options and Options.SkipBytefallFallback == true then
        BytefallStatus = "Bytefall fallback is managed by the host integration"
    else
        Fallback = ValmDecompiler.GetBytefallFallback()
        if type(Fallback) == "function" then
            local FallbackSuccess, FallbackResult = pcall(Fallback, Source, Bytecode, Options)
            if FallbackSuccess and type(FallbackResult) == "string" and FallbackResult ~= "" then
                ValmDecompiler.LastError = nil
                return FallbackResult
            end
            if not FallbackSuccess then
                NativeError = NativeError .. " | Bytefall: " .. tostring(FallbackResult)
            else
                NativeError = NativeError .. " | Bytefall returned no source"
            end
        end
        BytefallStatus = type(Fallback) == "function" and "Bytefall failed" or "Bytefall fallback is not connected. Register the local Bytefall function with ValmDecompiler.SetBytefallFallback(callback)"
    end
    ValmDecompiler.LastError = tostring(NativeError or "Native reconstruction failed") .. " | " .. BytefallStatus
    return nil, ValmDecompiler.LastError
end
function ValmDecompiler.DecompileAsync(Source, Options, Callback)
    if type(task) ~= "table" or type(task.spawn) ~= "function" then
        return false, "task.spawn is unavailable in this executor"
    end
    if Callback ~= nil and type(Callback) ~= "function" then
        return false, "Callback must be a function or nil"
    end
    task.spawn(function()
        local Result, ErrorMessage = ValmDecompiler.Decompile(Source, Options)
        if Callback then
            pcall(Callback, Result, ErrorMessage)
        end
    end)
    return true
end
function ValmDecompiler.ClearCache()
    for Key in pairs(Cache) do
        Cache[Key] = nil
    end
    table.clear(CacheOrder)
end
function ValmDecompiler.GetStatus()
    local Fallback = ValmDecompiler.GetBytefallFallback()
    return {
        Name = ValmDecompiler.Name,
        Version = ValmDecompiler.Version,
        BytecodeVersions = tostring(BytecodeVersionMin) .. "-" .. tostring(BytecodeVersionMax),
        RobloxOpcodeNormalization = true,
        RobloxOpcodeMultiplier = RobloxOpcodeMultiplier,
        BytefallConnected = type(Fallback) == "function",
        NativeDecompiler = "Structured control flow, SSA-style register versions, inline local declarations, protected-call result naming, debug-local lifetime tracking, semantic local naming, varargs, table reconstruction, and constant folding",
        SemanticLocalNaming = true,
        Disassembler = "Luau bytecode versions 3 through 14",
        CooperativeYield = type(task) == "table" and type(task.wait) == "function",
        UserInterface = false,
        ExternalDecompilerAPI = false
    }
end
local function DecompileBridge(Source, Options)
    local Result, ErrorMessage = ValmDecompiler.Decompile(Source, Options)
    if Result == nil then
        error("Valm Decompiler: " .. tostring(ErrorMessage), 2)
    end
    return Result
end
local function DisassembleBridge(Source, ProtoIndex)
    local Result, ErrorMessage = ValmDecompiler.Disassemble(Source, ProtoIndex)
    if Result == nil then
        error("Valm Decompiler: " .. tostring(ErrorMessage), 2)
    end
    return Result
end
Env.ValmDecompiler = ValmDecompiler
Env.ValmDecompilerInstalledDecompile = DecompileBridge
Env.decompile = DecompileBridge
Env.disassemble = DisassembleBridge
if type(_G) == "table" then
    _G.ValmDecompiler = ValmDecompiler
    _G.ValmDecompilerInstalledDecompile = DecompileBridge
    _G.decompile = DecompileBridge
    _G.disassemble = DisassembleBridge
end
return ValmDecompiler

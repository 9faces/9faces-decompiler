local Env = (type(getgenv) == "function" and getgenv()) or _G
local GetScriptBytecode = Env.getscriptbytecode or Env.dumpstring or getscriptbytecode or dumpstring
local Cache = setmetatable({}, {__mode = "k"})
local CacheOrder = {}
local CacheLimit = 24
local MaxBytecodeBytes = 1048576
local MaxPrototypes = 2048
local MaxStrings = 32768
local MaxInstructions = 75000
local MaxOutputLines = 6000
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
for _, Name in ipairs({"GETGLOBAL", "SETGLOBAL", "GETIMPORT", "GETTABLEKS", "SETTABLEKS", "NAMECALL", "NEWTABLE", "SETLIST", "FORGLOOP", "FASTCALL3", "LOADKX", "FASTCALL2", "FASTCALL2K", "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "GETUDATAKS", "SETUDATAKS", "NAMECALLUDATA", "NEWCLASSMEMBER", "CALLFB", "CMPPROTO", "NEWCLASS", "CONSTRUCT", "GETPRIVATEFIELD", "SETPRIVATEFIELD"}) do
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
local function SkipVarInt64(Reader)
    for _ = 1, 10 do
        local Byte = ReadByte(Reader)
        if Byte < 128 then
            return
        end
    end
    error("64-bit varint exceeds ten bytes", 0)
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
local function ParseBytecode(Data)
    if type(Data) ~= "string" then
        error("Bytecode must be a string", 0)
    end
    if #Data < 3 then
        error("Bytecode is empty or truncated", 0)
    end
    if #Data > MaxBytecodeBytes then
        error("Bytecode exceeds the 2 MiB safety limit", 0)
    end
    local Reader = NewReader(Data)
    local Version = ReadByte(Reader)
    if Version == 0 then
        error("Compiler error: " .. Data:sub(2), 0)
    end
    if Version < BytecodeVersionMin or Version > BytecodeVersionMax then
        error("9faces supports bytecode versions " .. tostring(BytecodeVersionMin) .. " through " .. tostring(BytecodeVersionMax) .. "; received version " .. tostring(Version), 0)
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
    for _, Proto in ipairs(Protos) do
        DecodeInstructions(Proto)
    end
    return {Version = Version, TypeVersion = TypeVersion, Strings = Strings, Protos = Protos, MainProto = MainProto, MainProtoIndex = MainProtoIndex, TotalInstructions = TotalInstructions}
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
    elseif Constant.Kind == "String" then
        return Quote(Constant.Value or "")
    elseif Constant.Kind == "Vector" or Constant.Kind == "VectorD" then
        local V = Constant.Value
        return "Vector3.new(" .. tostring(V[1]) .. ", " .. tostring(V[2]) .. ", " .. tostring(V[3]) .. ")"
    elseif Constant.Kind == "Table" or Constant.Kind == "TableWithConstants" then
        return "{}"
    elseif Constant.Kind == "Import" then
        local Import = Constant.Value
        local Length = math.floor(Import / 1073741824) % 4
        local Parts = {}
        local Masks = {Import % 1024, math.floor(Import / 1024) % 1024, math.floor(Import / 1048576) % 1024}
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
    local Base = "Local" .. tostring(Register + 1)
    local Name = Base
    local Suffix = 2
    while UsedNames[Name] do
        Name = Base .. tostring(Suffix)
        Suffix = Suffix + 1
    end
    UsedNames[Name] = true
    return Name
end
local function ReconstructLinear(Proto, Strings, Options)
    local UsePascalCase = not Options or Options.PascalCase ~= false
    local Lines = {}
    local Registers = {}
    local Declared = {}
    local UsedNames = {}
    local NameCalls = {}
    local Params = {}
    for Register = 0, Proto.NumParams - 1 do
        local Name = GetDebugLocalName(Proto, Register, 0, UsedNames, UsePascalCase)
        Params[#Params + 1] = Name
        Registers[Register] = Name
        Declared[Register] = true
    end
    local function GetReg(Register)
        local Value = Registers[Register]
        if not Value then
            return "Register" .. tostring(Register + 1)
        end
        return Value
    end
    local function WriteReg(Register, Expression, PC)
        local Name = Registers[Register]
        if not Name then
            Name = GetDebugLocalName(Proto, Register, PC, UsedNames, UsePascalCase)
            Registers[Register] = Name
        end
        if Declared[Register] then
            Lines[#Lines + 1] = Name .. " = " .. Expression
        else
            Lines[#Lines + 1] = "local " .. Name .. " = " .. Expression
            Declared[Register] = true
        end
        return Name
    end
    local function GetProperty(Base, Property)
        if IsIdentifier(Property) then
            return Base .. "." .. Property
        end
        return Base .. "[" .. Quote(Property) .. "]"
    end
    local HasReturn = false
    for _, Instruction in ipairs(Proto.Instructions) do
        YieldControl()
        local Name = Instruction.Name
        local A, B, C = Instruction.A, Instruction.B, Instruction.C
        local PC = Instruction.PC
        local Aux = Instruction.Aux
        if ControlFlowOpcodes[Instruction.Opcode] then
            return nil, "Control-flow reconstruction is not available for " .. Name
        elseif Name == "NOP" or Name == "BREAK" or Name == "CLOSEUPVALS" or Name == "PREPVARARGS" or Name == "COVERAGE" or Name == "NATIVECALL" or Name == "FASTCALL" or Name == "FASTCALL1" or Name == "FASTCALL2" or Name == "FASTCALL2K" or Name == "FASTCALL3" or Name == "FASTPCALL" then
        elseif Name == "LOADNIL" then
            WriteReg(A, "nil", PC)
        elseif Name == "LOADB" then
            if C ~= 0 then
                return nil, "Conditional LOADB requires control-flow reconstruction"
            end
            WriteReg(A, B ~= 0 and "true" or "false", PC)
        elseif Name == "LOADN" then
            WriteReg(A, tostring(Instruction.D), PC)
        elseif Name == "LOADK" then
            WriteReg(A, ConstantExpression(Proto, Instruction.D, Strings), PC)
        elseif Name == "LOADKX" then
            WriteReg(A, ConstantExpression(Proto, Aux, Strings), PC)
        elseif Name == "MOVE" then
            WriteReg(A, GetReg(B), PC)
        elseif Name == "GETGLOBAL" then
            local Key = GetConstant(Proto, Aux % 16777216)
            if Key.Kind ~= "String" then
                return nil, "GETGLOBAL does not reference a string constant"
            end
            local Expression = IsIdentifier(Key.Value) and Key.Value or "_G[" .. Quote(Key.Value) .. "]"
            WriteReg(A, Expression, PC)
        elseif Name == "SETGLOBAL" then
            local Key = GetConstant(Proto, Aux % 16777216)
            if Key.Kind ~= "String" then
                return nil, "SETGLOBAL does not reference a string constant"
            end
            local Expression = IsIdentifier(Key.Value) and Key.Value or "_G[" .. Quote(Key.Value) .. "]"
            Lines[#Lines + 1] = Expression .. " = " .. GetReg(A)
        elseif Name == "GETUPVAL" then
            local UpvalueName = Proto.DebugUpvalues[B + 1] or ("Upvalue" .. tostring(B + 1))
            WriteReg(A, UsePascalCase and PascalCase(UpvalueName) or UpvalueName, PC)
        elseif Name == "SETUPVAL" then
            local UpvalueName = Proto.DebugUpvalues[B + 1] or ("Upvalue" .. tostring(B + 1))
            Lines[#Lines + 1] = (UsePascalCase and PascalCase(UpvalueName) or UpvalueName) .. " = " .. GetReg(A)
        elseif Name == "GETTABLEKS" or Name == "GETUDATAKS" then
            local ConstantIndex = Name == "GETUDATAKS" and (Aux % 65536) or Aux
            local Key = GetConstant(Proto, ConstantIndex)
            if Key.Kind ~= "String" then
                return nil, Name .. " does not reference a string constant"
            end
            WriteReg(A, GetProperty(GetReg(B), Key.Value), PC)
        elseif Name == "GETTABLE" then
            WriteReg(A, GetReg(B) .. "[" .. GetReg(C) .. "]", PC)
        elseif Name == "GETTABLEN" then
            WriteReg(A, GetReg(B) .. "[" .. tostring(C + 1) .. "]", PC)
        elseif Name == "SETTABLEKS" or Name == "SETUDATAKS" then
            local ConstantIndex = Name == "SETUDATAKS" and (Aux % 65536) or Aux
            local Key = GetConstant(Proto, ConstantIndex)
            if Key.Kind ~= "String" then
                return nil, Name .. " does not reference a string constant"
            end
            Lines[#Lines + 1] = GetProperty(GetReg(B), Key.Value) .. " = " .. GetReg(A)
        elseif Name == "SETTABLE" then
            Lines[#Lines + 1] = GetReg(B) .. "[" .. GetReg(C) .. "] = " .. GetReg(A)
        elseif Name == "SETTABLEN" then
            Lines[#Lines + 1] = GetReg(B) .. "[" .. tostring(C + 1) .. "] = " .. GetReg(A)
        elseif Name == "ADD" or Name == "SUB" or Name == "MUL" or Name == "DIV" or Name == "MOD" or Name == "POW" or Name == "IDIV" or Name == "AND" or Name == "OR" then
            local Operators = {ADD = "+", SUB = "-", MUL = "*", DIV = "/", MOD = "%", POW = "^", IDIV = "//", AND = "and", OR = "or"}
            WriteReg(A, "(" .. GetReg(B) .. " " .. Operators[Name] .. " " .. GetReg(C) .. ")", PC)
        elseif Name == "ADDK" or Name == "SUBK" or Name == "MULK" or Name == "DIVK" or Name == "MODK" or Name == "POWK" or Name == "IDIVK" or Name == "ANDK" or Name == "ORK" then
            local Operators = {ADDK = "+", SUBK = "-", MULK = "*", DIVK = "/", MODK = "%", POWK = "^", IDIVK = "//", ANDK = "and", ORK = "or"}
            WriteReg(A, "(" .. GetReg(B) .. " " .. Operators[Name] .. " " .. ConstantExpression(Proto, C, Strings) .. ")", PC)
        elseif Name == "SUBRK" or Name == "DIVRK" then
            local Operator = Name == "SUBRK" and "-" or "/"
            WriteReg(A, "(" .. ConstantExpression(Proto, B, Strings) .. " " .. Operator .. " " .. GetReg(C) .. ")", PC)
        elseif Name == "NOT" then
            WriteReg(A, "(not " .. GetReg(B) .. ")", PC)
        elseif Name == "MINUS" then
            WriteReg(A, "(-" .. GetReg(B) .. ")", PC)
        elseif Name == "LENGTH" then
            WriteReg(A, "(#" .. GetReg(B) .. ")", PC)
        elseif Name == "CONCAT" then
            local Parts = {}
            for Register = B, C do
                Parts[#Parts + 1] = GetReg(Register)
            end
            WriteReg(A, "(" .. table.concat(Parts, " .. ") .. ")", PC)
        elseif Name == "NEWTABLE" then
            WriteReg(A, "{}", PC)
        elseif Name == "DUPTABLE" then
            WriteReg(A, "{}", PC)
        elseif Name == "GETIMPORT" then
            WriteReg(A, ConstantExpression(Proto, Instruction.D, Strings), PC)
        elseif Name == "NAMECALL" or Name == "NAMECALLUDATA" then
            local ConstantIndex = Name == "NAMECALLUDATA" and (Aux % 65536) or Aux
            local MethodConstant = GetConstant(Proto, ConstantIndex)
            if MethodConstant.Kind ~= "String" then
                return nil, Name .. " does not reference a string method name"
            end
            NameCalls[A] = {Receiver = GetReg(B), Method = MethodConstant.Value}
        elseif Name == "CALL" or Name == "CALLFB" then
            if B == 0 or C == 0 then
                return nil, "Variable-argument or variable-return CALL requires advanced reconstruction"
            end
            local MethodCall = NameCalls[A]
            local FirstArgument = A + (MethodCall and 2 or 1)
            local Arguments = {}
            for Register = FirstArgument, A + B - 1 do
                Arguments[#Arguments + 1] = GetReg(Register)
            end
            local Call
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
                Call = GetReg(A) .. "(" .. table.concat(Arguments, ", ") .. ")"
            end
            local ResultCount = C - 1
            if ResultCount == 0 then
                Lines[#Lines + 1] = Call
            elseif ResultCount == 1 then
                WriteReg(A, Call, PC)
            elseif ResultCount <= 16 then
                local ResultNames = {}
                local HasUndeclared = false
                for Register = A, A + ResultCount - 1 do
                    local ResultName = Registers[Register]
                    if not ResultName then
                        ResultName = GetDebugLocalName(Proto, Register, PC, UsedNames, UsePascalCase)
                        Registers[Register] = ResultName
                    end
                    if not Declared[Register] then
                        HasUndeclared = true
                        Declared[Register] = true
                    end
                    ResultNames[#ResultNames + 1] = ResultName
                end
                if HasUndeclared then
                    Lines[#Lines + 1] = "local " .. table.concat(ResultNames, ", ")
                end
                Lines[#Lines + 1] = table.concat(ResultNames, ", ") .. " = " .. Call
            else
                return nil, "CALL produces more than sixteen results"
            end
        elseif Name == "RETURN" then
            HasReturn = true
            if B == 0 then
                return nil, "Variable-return RETURN requires advanced reconstruction"
            end
            local Values = {}
            for Register = A, A + B - 2 do
                Values[#Values + 1] = GetReg(Register)
            end
            if #Values == 0 then
                Lines[#Lines + 1] = "return"
            else
                Lines[#Lines + 1] = "return " .. table.concat(Values, ", ")
            end
        elseif Name == "GETVARARGS" then
            if B <= 1 then
                return nil, "Variable-count GETVARARGS requires advanced reconstruction"
            end
            local VarargNames = {}
            local HasUndeclared = false
            for Register = A, A + B - 2 do
                local VarargName = Registers[Register]
                if not VarargName then
                    VarargName = GetDebugLocalName(Proto, Register, PC, UsedNames, UsePascalCase)
                    Registers[Register] = VarargName
                end
                if not Declared[Register] then
                    HasUndeclared = true
                    Declared[Register] = true
                end
                VarargNames[#VarargNames + 1] = VarargName
            end
            if HasUndeclared then
                Lines[#Lines + 1] = "local " .. table.concat(VarargNames, ", ")
            end
            Lines[#Lines + 1] = table.concat(VarargNames, ", ") .. " = ..."
        elseif Name == "NEWCLOSURE" or Name == "DUPCLOSURE" or Name == "CAPTURE" then
            return nil, "Nested function reconstruction requires advanced analysis"
        elseif Name == "SETLIST" or Name == "NEWCLASS" or Name == "CONSTRUCT" or Name == "FINCONSTRUCT" or Name == "NEWCLASSMEMBER" or Name == "GETPRIVATEFIELD" or Name == "SETPRIVATEFIELD" then
            return nil, "Advanced opcode " .. Name .. " requires fallback reconstruction"
        else
            return nil, "Native reconstruction does not yet support " .. Name
        end
        if #Lines > MaxOutputLines then
            return nil, "Reconstructed source exceeds the output safety limit"
        end
    end
    if not HasReturn and #Lines == 0 then
        return ""
    end
    return table.concat(Lines, "\n")
end
local function DisassembleParsed(Parsed, SelectedProto)
    local Lines = {
        "9faces Disassembly",
        "Bytecode Version: " .. tostring(Parsed.Version),
        "Type Version: " .. tostring(Parsed.TypeVersion),
        "Prototype Count: " .. tostring(#Parsed.Protos),
        "Instruction Count: " .. tostring(Parsed.TotalInstructions),
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
    if type(GetScriptBytecode) ~= "function" then
        error("This executor does not expose getscriptbytecode or dumpstring", 0)
    end
    local Success, Result = pcall(GetScriptBytecode, Source)
    if not Success then
        error("Bytecode capture failed: " .. tostring(Result), 0)
    end
    if type(Result) ~= "string" then
        error("The executor returned no bytecode for this script", 0)
    end
    return Result
end
local function FindBytefall()
    local Candidates = {
        Env.Bytefall,
        Env.ByteFall,
        Env.bytefall,
        Env.BytefallDecompiler,
        Env.ByteFallDecompiler,
        Env.BytefallDecompile,
        Env.ByteFallDecompile,
        Env.bytefall_decompile,
        Env.Bytefall_Decompile,
        Env.BytefallFallback,
        Env.ByteFallFallback,
        Env.bytefallFallback,
        Env.BytefallAPI,
        _G.Bytefall,
        _G.ByteFall,
        _G.bytefall,
        _G.BytefallDecompiler,
        _G.BytefallDecompile,
        _G.ByteFallDecompiler
    }
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
local Ninefaces = {
    Name = "9faces Decompiler",
    Version = "0.2.0-alpha",
    BytecodeVersionMin = BytecodeVersionMin,
    BytecodeVersionMax = BytecodeVersionMax,
    BytefallFallback = nil,
    LastError = nil,
    FormatIdentifier = PascalCase,
    OpcodeNames = OpcodeNames,
    CacheLimit = CacheLimit,
    MaximumBytecodeBytes = MaxBytecodeBytes,
    MaximumInstructions = MaxInstructions,
    Cache = Cache
}
function Ninefaces.SetBytefallFallback(Callback)
    if Callback ~= nil and type(Callback) ~= "function" then
        error("Bytefall fallback must be a function or nil", 2)
    end
    Ninefaces.BytefallFallback = Callback
end
function Ninefaces.GetBytefallFallback()
    return Ninefaces.BytefallFallback or FindBytefall()
end
function Ninefaces.Parse(Source)
    local Bytecode = GetBytecode(Source)
    YieldCounter = 0
    return ParseBytecode(Bytecode)
end
function Ninefaces.Inspect(Source)
    local Success, Result = pcall(function()
        local Parsed = Ninefaces.Parse(Source)
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
        Ninefaces.LastError = tostring(Result)
        return nil, Ninefaces.LastError
    end
    Ninefaces.LastError = nil
    return Result
end
function Ninefaces.Disassemble(Source, ProtoIndex)
    local Success, Result = pcall(function()
        local Parsed = Ninefaces.Parse(Source)
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
        Ninefaces.LastError = tostring(Result)
        return nil, Ninefaces.LastError
    end
    Ninefaces.LastError = nil
    return Result
end
function Ninefaces.Decompile(Source, Options)
    if type(Options) ~= "table" then
        Options = nil
    end
    local Bytecode
    local Success, CaptureResult = pcall(GetBytecode, Source)
    if not Success then
        Ninefaces.LastError = tostring(CaptureResult)
        return nil, Ninefaces.LastError
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
        return ReconstructLinear(Parsed.MainProto, Parsed.Strings, Options)
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
        Ninefaces.LastError = nil
        return NativeSource
    end
    local Fallback = Ninefaces.GetBytefallFallback()
    if type(Fallback) == "function" then
        local FallbackSuccess, FallbackResult = pcall(Fallback, Source, Bytecode, Options)
        if FallbackSuccess and type(FallbackResult) == "string" and FallbackResult ~= "" then
            Ninefaces.LastError = nil
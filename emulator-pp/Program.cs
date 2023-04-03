using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures.Types;
using AsmResolver.PE.DotNet.Cil;
using Echo.Memory;
using Echo.Platforms.AsmResolver.Emulation;
using Echo.Platforms.AsmResolver.Emulation.Dispatch;
using Echo.Platforms.AsmResolver.Emulation.Invocation;
using System.Reflection;
using System.Text;

namespace emulator_pp {
    internal static class Program {

#pragma warning disable CS8618
        private static ModuleDefinition _module;
        private static CilVirtualMachine _virtualMachine;
#pragma warning restore CS8618

        public static void Main(string[] args) {
            if (args.Length is 0) {
                Console.Write("Path: ");
                args = new string[] { Console.ReadLine()! };
            }


            _module = ModuleDefinition.FromFile(args[0]);
            // var is32Bit = module.IsBit32Preferred || module.IsBit32Required; (BUGGED).
            _virtualMachine = new CilVirtualMachine(_module, false);

            InitialRuntime();

            DecodeConstants();
        }

        private static void DecodeConstants() {

            var methods = _module.GetAllTypes()
                .SelectMany(t => t.Methods)
                .Where(m => m.CilMethodBody is not null);

            _virtualMachine.Dispatcher.BeforeInstructionDispatch += CallvirtPatcher;

            foreach (var method in methods) {
                var instructions = method.CilMethodBody!.Instructions;

                for (int i = 0; i < instructions.Count; i++) {
                    var instruction = instructions[i];

                    // NOTE: following code for testing only, arguments should be collected using proper dataflow graph to trace them correctly.

                    if (!instruction.IsLdcI4())
                        continue;

                    var brInstruction = instructions[i + 1];

                    if (!brInstruction.IsUnconditionalBranch())
                        continue;

                    var decoderInstruction = instructions[i + 2];

                    if (decoderInstruction.OpCode.Code is not CilCode.Call && decoderInstruction.Operand is not MethodSpecification)
                        continue;

                    var decoderMethod = (MethodSpecification)decoderInstruction.Operand!;

                    var result = _virtualMachine.Call(decoderMethod, new object[] { instruction.GetLdcI4Constant() });

                    if (result is null)
                        continue;

                    var stringHandle = result.AsObjectHandle(_virtualMachine);

                    var decodedConstant = _virtualMachine.ObjectMarshaller.ToObject<string>(stringHandle);

                    instruction.ReplaceWithNop();
                    brInstruction.ReplaceWithNop();

                    decoderInstruction.ReplaceWith(CilOpCodes.Ldstr, decodedConstant);

                }
            }

            _virtualMachine.Dispatcher.BeforeInstructionDispatch -= CallvirtPatcher;
        }

        private static void InitialRuntime() {

            var globalType = _module.GetOrCreateModuleType();

            var initializeBuffer = globalType.Methods.FirstOrDefault(method => !method.Signature!.ReturnsValue);
            var decodeBuffer = globalType.Methods.FirstOrDefault(method => method.GenericParameters.Any());
            var decompressBuffer = globalType.Methods.FirstOrDefault(method => method.Signature!.ReturnType is SzArrayTypeSignature);

            if (initializeBuffer is null || decodeBuffer is null || decompressBuffer is null) {
                throw new InvalidOperationException("Invalid confuser-ex sample.");
            }

            var decodeBufferInvocations = new[] {
                decodeBuffer.CilMethodBody!.Instructions.First(instruction => instruction.Operand is MemberReference member && member.Name == $"get_{nameof(Encoding.UTF8)}").Operand,
                decodeBuffer.CilMethodBody!.Instructions.First(instruction => instruction.Operand is MemberReference member && member.Name == nameof(Assembly.GetExecutingAssembly)).Operand,
                decodeBuffer.CilMethodBody!.Instructions.First(instruction => instruction.Operand is MemberReference member && member.Name == nameof(Assembly.GetCallingAssembly)).Operand,
                decodeBuffer.CilMethodBody!.Instructions.First(instruction => instruction.Operand is MemberReference member && member.Name == nameof(object.Equals)).Operand,
            }.Select(member => (IMethodDescriptor)member!);

            var getEncodingString = (IMethodDescriptor)decodeBuffer.CilMethodBody!.Instructions.First(instruction => instruction.Operand is MemberReference member && member.Name == nameof(Encoding.GetString)).Operand!;

            var cctor = _module.GetModuleConstructor()!;

            var runtimeHelpersArray = (IMethodDescriptor)initializeBuffer.CilMethodBody!.Instructions.First(i => i.OpCode.Code is CilCode.Call).Operand!;

            var invoker = DefaultInvokers.CreateShim()
                .Map(runtimeHelpersArray, InitializeArray)
                .Map(decompressBuffer, LzmaDecompress)
                .Map(getEncodingString, GetUtf8String)
                .MapMany(decodeBufferInvocations, ReturnTrue)
                .WithFallback(DefaultInvokers.ReturnUnknown);

            _virtualMachine.Invoker = invoker;

            _virtualMachine.Call(initializeBuffer, Array.Empty<object>());

        }

        private static void CallvirtPatcher(object? sender, CilDispatchEventArgs arguments) {
            // string stack = string.Join(", ", e.Context.CurrentFrame.EvaluationStack);
            // Console.WriteLine($"{e.Instruction,-100} {{{stack}}}");

            var argumentInstruction = arguments.Instruction;

            if (argumentInstruction is null || argumentInstruction.Operand is null) {
                return;
            }

            if (argumentInstruction.Operand is IMethodDescriptor method && (method.Name == nameof(object.Equals) || method.Name == nameof(Encoding.GetString))) {
                argumentInstruction.OpCode = CilOpCodes.Call;
            }
        }

        private static InvocationResult ReturnTrue(CilExecutionContext context, IMethodDescriptor method, IList<BitVector> arguments) {
            return InvocationResult.StepOver(_virtualMachine.ObjectMarshaller.ToBitVector(true));
        }

        private static InvocationResult InitializeArray(CilExecutionContext context, IMethodDescriptor method, IList<BitVector> arguments) {
            // patchs RuntimeHelpers::InitializeArray(Array,RuntimeFieldHandle)
            var arrayHandle = arguments[0].AsObjectHandle(_virtualMachine);
            var fieldHandle = arguments[1].AsStructHandle(_virtualMachine);

            if (_virtualMachine.ValueFactory.ClrMockMemory.Fields.TryGetObject(fieldHandle.Address, out var field)) {
                byte[] data = field!.Resolve()!.FieldRva!.WriteIntoArray();
                arrayHandle.WriteArrayData(data);
            }

            return InvocationResult.StepOver(null);
        }

        private static InvocationResult LzmaDecompress(CilExecutionContext context, IMethodDescriptor method, IList<BitVector> arguments) {
            // patchs Lzma::Decompress(uint8[])
            var data = _virtualMachine.ObjectMarshaller.ToObject<byte[]>(arguments[0]);
            return InvocationResult.StepOver(_virtualMachine.ObjectMarshaller.ToBitVector(Lzma.Decompress(data!)));
        }

        private static InvocationResult GetUtf8String(CilExecutionContext context, IMethodDescriptor method, IList<BitVector> arguments) {
            // patchs UTF8Encoding::GetString(uint8[],int32,int32)
            // var span = _virtualMachine.StaticFields.GetFieldSpan(_module.GetModuleType().Fields.First());
            // _virtualMachine.ObjectMarshaller.ToObject<byte[]>(span);
            var buffer = _virtualMachine.ObjectMarshaller.ToObject<byte[]>(arguments[1]);
            var index = _virtualMachine.ObjectMarshaller.ToObject<int>(arguments[2]);
            var count = _virtualMachine.ObjectMarshaller.ToObject<int>(arguments[3]);
            return InvocationResult.StepOver(_virtualMachine.ObjectMarshaller.ToBitVector(Encoding.UTF8.GetString(buffer!, index, count)));
        }
    }
}
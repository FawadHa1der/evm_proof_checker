// Shared in-process EVM harness. Installs the kernel via state injection when
// it exceeds EIP-170. This bypasses deployment limits for logical testing;
// Cancun opcode execution is NOT a full Glamsterdam simulation. Transaction
// envelope estimates for the draft fork are separate in budgets.js.
'use strict';

const { VM } = require('@ethereumjs/vm');
const { Common, Hardfork, Chain } = require('@ethereumjs/common');
const { hexToBytes, bytesToHex, Address, Account } = require('@ethereumjs/util');

const CALLER = Address.fromString('0x1000000000000000000000000000000000000001');
const KERNEL_ADDR = Address.fromString('0x4e61000000000000000000000000000000000001');

async function makeVm() {
  const common = new Common({ chain: Chain.Mainnet, hardfork: Hardfork.Cancun });
  const vm = await VM.create({ common });
  await vm.stateManager.putAccount(CALLER, new Account());
  return vm;
}

async function installKernel(vm, artifacts) {
  const sm = vm.stateManager;
  await sm.putAccount(KERNEL_ADDR, new Account());
  const code = hexToBytes(artifacts.LeanKernel.deployed);
  if (sm.putContractCode) await sm.putContractCode(KERNEL_ADDR, code);
  else await sm.putCode(KERNEL_ADDR, code);
  return KERNEL_ADDR;
}

async function deployContract(vm, bytecodeHex, ctorArgsHex = '') {
  const r = await vm.evm.runCall({
    caller: CALLER,
    gasLimit: 10_000_000_000n,
    data: hexToBytes(bytecodeHex + ctorArgsHex.replace(/^0x/, '')),
  });
  if (r.execResult.exceptionError) {
    throw new Error('deploy failed: ' + r.execResult.exceptionError.error);
  }
  return r.createdAddress;
}

async function callContract(vm, to, calldataHex, gasLimit = 10_000_000_000n) {
  return vm.evm.runCall({ caller: CALLER, to, gasLimit, data: hexToBytes(calldataHex) });
}

module.exports = { makeVm, installKernel, deployContract, callContract, CALLER, KERNEL_ADDR, bytesToHex };

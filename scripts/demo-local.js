// End-to-end local deployment demo (no external node needed):
// installs LeanKernel + deploys TheoremRegistry in an in-process EVM,
// submits an export through the registry as a real transaction, and shows
// the resulting on-chain record. Default export: 048_eqRuleK (Eq + Bool +
// K-style recursor reduction).
'use strict';

const fs = require('fs');
const path = require('path');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, REGISTRY_ABI, VERDICT } = require('../tools/lib');
const { build } = require('../tools/build');
const { makeVm, installKernel, deployContract, callContract, bytesToHex } = require('../tools/evm');

async function main() {
  const a = build();
  const vm = await makeVm();
  const kernelAddr = await installKernel(vm, a);
  console.log(`LeanKernel       installed at ${kernelAddr}  (${a.LeanKernel.deployedSize} bytes` +
    (a.LeanKernel.deployedSize > 24576 ? ', EIP-7907/L2-class size' : '') + ')');
  const ctor = new ethers.AbiCoder().encode(['address'], [kernelAddr.toString()]);
  const regAddr = await deployContract(vm, a.TheoremRegistry.bytecode, ctor);
  console.log(`TheoremRegistry  deployed at  ${regAddr}  (${a.TheoremRegistry.deployedSize} bytes)`);

  const file = process.argv[2] || path.join(__dirname, '..', 'tests', 'good', '048_eqRuleK.ndjson');
  const enc = encodeForChain(parseNdjson(fs.readFileSync(file, 'utf8')));
  const args = [enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab];
  const iface = new ethers.Interface(REGISTRY_ABI);

  const tx = await callContract(vm, regAddr, iface.encodeFunctionData('submit', args), 1_000_000_000n);
  if (tx.execResult.exceptionError) throw new Error('submit failed: ' + tx.execResult.exceptionError.error);
  const [verdict] = iface.decodeFunctionResult('submit', bytesToHex(tx.execResult.returnValue));
  console.log(`\nregistry.submit(${path.basename(file)}): verdict=${VERDICT[Number(verdict)]}, gas=${tx.execResult.executionGasUsed}`);

  const hr = await callContract(vm, regAddr, iface.encodeFunctionData('exportHashOf', args));
  const [hash] = iface.decodeFunctionResult('exportHashOf', bytesToHex(hr.execResult.returnValue));
  const cq = await callContract(vm, regAddr, iface.encodeFunctionData('isChecked', [hash]));
  const [checked] = iface.decodeFunctionResult('isChecked', bytesToHex(cq.execResult.returnValue));
  console.log(`exportHash ${hash}`);
  console.log(`isChecked  ${checked}  ← permanent on-chain record that this export type-checked`);
}

main().catch((e) => { console.error(e); process.exit(1); });

'use strict';

const fs = require('fs');
const { createHash } = require('crypto');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, REASONS } = require('./lib');
const { build } = require('./build');
const { makeVm, installKernel, callContract, bytesToHex } = require('./evm');
const { DEFAULT_GAS_LIMIT, transactionBudget, CODE_SIZE_LIMIT, INITCODE_SIZE_LIMIT } = require('./budgets');

function normalizeResult(result, iface) {
  const gas = result.execResult.executionGasUsed;
  const exception = result.execResult.exceptionError;
  if (exception) {
    const error = String(exception.error);
    const resource = error === 'out of gas' || error === 'stack overflow';
    return {
      verdict: resource ? 2 : 3, failedDecl: 0n, gas,
      category: resource ? 'evm-resource' : 'fault',
      reason: `EVM ${error}`,
    };
  }
  const [verdict, failedDecl, reason] = iface.decodeFunctionResult('check', bytesToHex(result.execResult.returnValue));
  const v = Number(verdict);
  const why = REASONS[Number(reason)] || String(reason);
  if (![0, 1, 2, 3].includes(v)) throw new Error(`invalid contract verdict ${v}`);
  return {
    verdict: v === 3 ? 2 : v, contractVerdict: v, failedDecl, gas,
    category: v === 3 ? 'kernel-resource' : v === 2 ? 'unsupported' : 'checked',
    reason: why,
  };
}

async function makeChecker() {
  const artifacts = build();
  const vm = await makeVm();
  const kernelAddr = await installKernel(vm, artifacts);
  const iface = new ethers.Interface(KERNEL_ABI);
  return { artifacts, vm, kernelAddr, iface };
}

async function checkFile(file, checker, { maxBytes = 0, gasLimit = DEFAULT_GAS_LIMIT, profile = 'local' } = {}) {
  if (!['local', 'glamsterdam'].includes(profile)) throw new Error(`unknown profile: ${profile}`);
  const bytes = fs.statSync(file).size;
  const decline = (category, reason) => ({ verdict: 2, failedDecl: 0n, gas: 0n, bytes, category, reason });
  if (maxBytes > 0 && bytes > maxBytes) return decline('size', `entrypoint size guard (${bytes} > ${maxBytes} bytes)`);

  const text = fs.readFileSync(file, 'utf8');
  const sha256 = createHash('sha256').update(text).digest('hex');
  let enc;
  try {
    const parsed = parseNdjson(text);
    const ver = parsed.meta && parsed.meta.format && parsed.meta.format.version;
    if (!ver || !String(ver).startsWith('3.')) return decline('format', `unsupported export format ${ver}`);
    enc = encodeForChain(parsed);
  } catch (error) {
    return decline('encoding', `cannot encode export: ${error.message}`);
  }

  const { iface, vm, kernelAddr, artifacts } = checker;
  const calldata = iface.encodeFunctionData('check', [
    enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab,
  ]);
  const budget = transactionBudget(calldata);
  if (profile === 'glamsterdam') {
    if (artifacts.LeanKernel.deployedSize > CODE_SIZE_LIMIT || artifacts.LeanKernel.initcodeSize > INITCODE_SIZE_LIMIT) {
      return { ...decline('code-size', 'kernel exceeds EIP-7954 code/initcode limits'), budget };
    }
    if (!budget.fitsTransaction) return { ...decline('calldata', 'calldata floor/intrinsic gas exceeds execution cap'), budget };
    if (gasLimit > budget.executionAllowance) gasLimit = budget.executionAllowance;
  }
  const result = normalizeResult(await callContract(vm, kernelAddr, calldata, gasLimit), iface);
  return { ...result, bytes, sha256, budget: transactionBudget(calldata, result.gas) };
}

function outcomeMatches(expected, verdict) {
  if (expected === 'either') return verdict === 0 || verdict === 1;
  if (expected === 'accept') return verdict === 0;
  if (expected === 'reject') return verdict === 1;
  if (expected === 'decline') return verdict === 2;
  throw new Error(`unknown expected outcome: ${expected}`);
}

module.exports = { makeChecker, checkFile, normalizeResult, outcomeMatches };

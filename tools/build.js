// Compiles contracts once and caches artifacts in build/.
'use strict';
const fs = require('fs');
const path = require('path');
const ROOT = path.join(__dirname, '..');

function build(force = false) {
  const outPath = path.join(ROOT, 'build', 'artifacts.json');
  const srcs = ['LeanKernel.sol', 'TheoremRegistry.sol'].map((f) =>
    fs.readFileSync(path.join(ROOT, 'contracts', f), 'utf8'));
  const crypto = require('crypto');
  const solc = require('solc');
  const compiler = { version: solc.version(), evmVersion: 'cancun', viaIR: true, optimizerRuns: 1 };
  const CACHE_VERSION = 'v4-pinned-compiler-settings';
  const hash = crypto.createHash('sha256').update(CACHE_VERSION + '\0' + JSON.stringify(compiler) + '\0' + srcs.join('\0')).digest('hex');
  if (!force && fs.existsSync(outPath)) {
    const cached = JSON.parse(fs.readFileSync(outPath, 'utf8'));
    if (cached.sourceHash === hash) return cached;
  }
  const input = {
    language: 'Solidity',
    sources: {
      'LeanKernel.sol': { content: srcs[0] },
      'TheoremRegistry.sol': { content: srcs[1] },
    },
    settings: {
      evmVersion: compiler.evmVersion,
      optimizer: { enabled: true, runs: 1 },
      viaIR: true,
      outputSelection: { '*': { '*': ['abi', 'evm.bytecode.object', 'evm.deployedBytecode.object'] } },
    },
  };
  const out = JSON.parse(solc.compile(JSON.stringify(input)));
  const errors = (out.errors || []).filter((e) => e.severity === 'error');
  if (errors.length) throw new Error(errors.map((e) => e.formattedMessage).join('\n'));
  const artifacts = {
    sourceHash: hash,
    compiler,
    LeanKernel: {
      abi: out.contracts['LeanKernel.sol'].LeanKernel.abi,
      bytecode: '0x' + out.contracts['LeanKernel.sol'].LeanKernel.evm.bytecode.object,
      deployed: '0x' + out.contracts['LeanKernel.sol'].LeanKernel.evm.deployedBytecode.object,
      initcodeSize: out.contracts['LeanKernel.sol'].LeanKernel.evm.bytecode.object.length / 2,
      deployedSize: out.contracts['LeanKernel.sol'].LeanKernel.evm.deployedBytecode.object.length / 2,
    },
    TheoremRegistry: {
      abi: out.contracts['TheoremRegistry.sol'].TheoremRegistry.abi,
      bytecode: '0x' + out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.bytecode.object,
      deployed: '0x' + out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.deployedBytecode.object,
      initcodeSize: out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.bytecode.object.length / 2,
      deployedSize: out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.deployedBytecode.object.length / 2,
    },
  };
  fs.mkdirSync(path.join(ROOT, 'build'), { recursive: true });
  fs.writeFileSync(outPath, JSON.stringify(artifacts));
  return artifacts;
}

if (require.main === module) {
  const a = build(true);
  const EIP170 = 24576;
  const { CODE_SIZE_LIMIT, INITCODE_SIZE_LIMIT } = require('./budgets');
  const status = (size, budget) => (size <= budget ? 'ok' : 'exceeds');
  console.log(`LeanKernel:      ${a.LeanKernel.deployedSize} bytes deployed, ${a.LeanKernel.initcodeSize} bytes initcode`);
  console.log(`TheoremRegistry: ${a.TheoremRegistry.deployedSize} bytes deployed, ${a.TheoremRegistry.initcodeSize} bytes initcode`);
  console.log(`EIP-170 budget:  ${EIP170} bytes (${status(a.LeanKernel.deployedSize, EIP170)})`);
  console.log(`EIP-7954 target: ${CODE_SIZE_LIMIT} bytes (${status(a.LeanKernel.deployedSize, CODE_SIZE_LIMIT)})`);
  console.log(`EIP-7954 initcode: ${INITCODE_SIZE_LIMIT} bytes (${status(a.LeanKernel.initcodeSize, INITCODE_SIZE_LIMIT)})`);
  if (a.LeanKernel.deployedSize > CODE_SIZE_LIMIT || a.LeanKernel.initcodeSize > INITCODE_SIZE_LIMIT) process.exitCode = 1;
}
module.exports = { build };

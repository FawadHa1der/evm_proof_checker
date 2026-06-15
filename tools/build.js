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
  const CACHE_VERSION = 'v2-with-deployed';
  const hash = crypto.createHash('sha256').update(CACHE_VERSION + '\0' + srcs.join('\0')).digest('hex');
  if (!force && fs.existsSync(outPath)) {
    const cached = JSON.parse(fs.readFileSync(outPath, 'utf8'));
    if (cached.sourceHash === hash) return cached;
  }
  const solc = require('solc');
  const input = {
    language: 'Solidity',
    sources: {
      'LeanKernel.sol': { content: srcs[0] },
      'TheoremRegistry.sol': { content: srcs[1] },
    },
    settings: {
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
    LeanKernel: {
      abi: out.contracts['LeanKernel.sol'].LeanKernel.abi,
      bytecode: '0x' + out.contracts['LeanKernel.sol'].LeanKernel.evm.bytecode.object,
      deployed: '0x' + out.contracts['LeanKernel.sol'].LeanKernel.evm.deployedBytecode.object,
      deployedSize: out.contracts['LeanKernel.sol'].LeanKernel.evm.deployedBytecode.object.length / 2,
    },
    TheoremRegistry: {
      abi: out.contracts['TheoremRegistry.sol'].TheoremRegistry.abi,
      bytecode: '0x' + out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.bytecode.object,
      deployed: '0x' + out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.deployedBytecode.object,
      deployedSize: out.contracts['TheoremRegistry.sol'].TheoremRegistry.evm.deployedBytecode.object.length / 2,
    },
  };
  fs.mkdirSync(path.join(ROOT, 'build'), { recursive: true });
  fs.writeFileSync(outPath, JSON.stringify(artifacts));
  return artifacts;
}

if (require.main === module) {
  const a = build(true);
  console.log(`LeanKernel:      ${a.LeanKernel.deployedSize} bytes deployed`);
  console.log(`TheoremRegistry: ${a.TheoremRegistry.deployedSize} bytes deployed`);
}
module.exports = { build };

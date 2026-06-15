// Checks a lean4export NDJSON file against a *deployed* LeanKernel, and
// optionally records it in the TheoremRegistry.
//
//   KERNEL=0x... RPC_URL=... node scripts/check-onchain.js file.ndjson
//   REGISTRY=0x... PRIVATE_KEY=0x... SUBMIT=1 ... → sends a real transaction
'use strict';

const fs = require('fs');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, REGISTRY_ABI, VERDICT, REASONS } = require('../tools/lib');

const EIP7825_TX_GAS_CAP = 16777216n;

async function main() {
  const file = process.argv[2];
  if (!file || !process.env.KERNEL) {
    console.error('usage: KERNEL=0x... [REGISTRY=0x... SUBMIT=1] RPC_URL=... node scripts/check-onchain.js <file.ndjson>');
    process.exit(1);
  }
  const provider = new ethers.JsonRpcProvider(process.env.RPC_URL || 'http://127.0.0.1:8545');
  const enc = encodeForChain(parseNdjson(fs.readFileSync(file, 'utf8')));
  const args = [enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab];

  const kernel = new ethers.Contract(process.env.KERNEL, KERNEL_ABI, provider);
  const [verdict, failedDecl, reason] = await kernel.check(...args);
  const gas = await kernel.check.estimateGas(...args).catch(() => null);
  console.log(`verdict: ${VERDICT[Number(verdict)]} (decl ${failedDecl}, ${REASONS[Number(reason)] || reason})` +
    (gas ? `, estimated gas ${gas}` : ''));
  if (gas && gas > EIP7825_TX_GAS_CAP) {
    console.warn(`warning: estimated gas exceeds the EIP-7825 per-transaction cap (${EIP7825_TX_GAS_CAP})`);
  }

  if (process.env.SUBMIT && process.env.REGISTRY && process.env.PRIVATE_KEY) {
    const wallet = new ethers.Wallet(process.env.PRIVATE_KEY, provider);
    const reg = new ethers.Contract(process.env.REGISTRY, REGISTRY_ABI, wallet);
    const tx = await reg.submit(...args);
    const rcpt = await tx.wait();
    const h = await reg.exportHashOf(...args);
    console.log(`registry tx ${rcpt.hash}: gasUsed=${rcpt.gasUsed}, exportHash=${h}, isChecked=${await reg.isChecked(h)}`);
  }
}

main().catch((e) => { console.error(e); process.exit(1); });

// Deploys LeanKernel + TheoremRegistry to any EVM chain over JSON-RPC.
//
//   RPC_URL=http://127.0.0.1:8545 PRIVATE_KEY=0x... node scripts/deploy.js
//
// Works with a local anvil/hardhat node, Sepolia, Base Sepolia, or any L2.
// (Sepolia RPC endpoints: https://ethereum-sepolia-rpc.publicnode.com,
//  Base Sepolia: https://sepolia.base.org — bring a funded key.)
'use strict';

const { ethers } = require('ethers');
const { build } = require('../tools/build');

const EIP170_CODE_SIZE = 24576;
const EIP7907_TARGET_CODE_SIZE = 65536;

async function main() {
  const rpc = process.env.RPC_URL || 'http://127.0.0.1:8545';
  const pk = process.env.PRIVATE_KEY;
  if (!pk) {
    console.error('set PRIVATE_KEY (and RPC_URL; defaults to local anvil at :8545)');
    process.exit(1);
  }
  const provider = new ethers.JsonRpcProvider(rpc);
  const wallet = new ethers.Wallet(pk, provider);
  const net = await provider.getNetwork();
  console.log(`deploying from ${wallet.address} to chain ${net.chainId} via ${rpc}`);

  const a = build();
  console.log(
    `LeanKernel deployed bytecode: ${a.LeanKernel.deployedSize} bytes ` +
    `(EIP-170 ${EIP170_CODE_SIZE}; EIP-7907 target ${EIP7907_TARGET_CODE_SIZE})`
  );
  if (a.LeanKernel.deployedSize > EIP7907_TARGET_CODE_SIZE) {
    throw new Error('LeanKernel exceeds the EIP-7907 target budget');
  }
  if (a.LeanKernel.deployedSize > EIP170_CODE_SIZE && process.env.ALLOW_EIP7907 !== '1') {
    throw new Error(
      'LeanKernel exceeds today\'s EIP-170 code-size limit. ' +
      'Set ALLOW_EIP7907=1 only when deploying to an EIP-7907/L2/devnet environment with a raised limit.'
    );
  }

  const kernelF = new ethers.ContractFactory(a.LeanKernel.abi, a.LeanKernel.bytecode, wallet);
  const kernel = await kernelF.deploy();
  await kernel.waitForDeployment();
  const kernelAddr = await kernel.getAddress();
  const kernelRcpt = await kernel.deploymentTransaction().wait();
  console.log(`LeanKernel:      ${kernelAddr}  (gas ${kernelRcpt.gasUsed})`);

  const regF = new ethers.ContractFactory(a.TheoremRegistry.abi, a.TheoremRegistry.bytecode, wallet);
  const reg = await regF.deploy(kernelAddr);
  await reg.waitForDeployment();
  const regAddr = await reg.getAddress();
  const regRcpt = await reg.deploymentTransaction().wait();
  console.log(`TheoremRegistry: ${regAddr}  (gas ${regRcpt.gasUsed})`);
  console.log('\nnext: KERNEL=' + kernelAddr + ' REGISTRY=' + regAddr +
    ' RPC_URL=' + rpc + ' PRIVATE_KEY=... node scripts/check-onchain.js tests/good/025_peano3.ndjson');
}

main().catch((e) => { console.error(e); process.exit(1); });

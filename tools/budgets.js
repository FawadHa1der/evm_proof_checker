'use strict';

const CODE_SIZE_LIMIT = 65536;
const INITCODE_SIZE_LIMIT = 131072;
const EXECUTION_GAS_CAP = 16777216n;
const DEFAULT_MAX_BYTES = 512000;
const DEFAULT_GAS_LIMIT = 10000000000n;

// Draft snapshot, 2026-09-11: EIP-7954, EIP-2780, EIP-7976, EIP-8037.
// Models a zero-value, non-delegated EOA call to the installed pure kernel,
// without access lists. It is not a full Glamsterdam execution client and
// must not be used to estimate deployment or TheoremRegistry state writes.
const MODEL = 'glamsterdam-draft-2026-09-11-direct-kernel';
const BASE_GAS = 15000n;
const FLOOR_PER_BYTE = 64n;

function transactionBudget(calldata, executionGas = 0n) {
  if (!/^0x(?:[0-9a-fA-F]{2})*$/.test(calldata)) throw new Error('invalid calldata hex');
  if (executionGas < 0n) throw new Error('negative execution gas');
  const bytes = Buffer.from(calldata.slice(2), 'hex');
  let zeroBytes = 0;
  for (const byte of bytes) if (byte === 0) zeroBytes++;
  const calldataGas = BigInt(zeroBytes) * 4n + BigInt(bytes.length - zeroBytes) * 16n;
  const intrinsicGas = BASE_GAS + calldataGas;
  const calldataFloorGas = BASE_GAS + BigInt(bytes.length) * FLOOR_PER_BYTE;
  const beforeFloor = intrinsicGas + executionGas;
  const estimatedTransactionGas = beforeFloor > calldataFloorGas ? beforeFloor : calldataFloorGas;
  return {
    model: MODEL,
    calldataBytes: bytes.length,
    zeroBytes,
    intrinsicGas,
    calldataFloorGas,
    executionGas,
    estimatedTransactionGas,
    executionAllowance: intrinsicGas < EXECUTION_GAS_CAP ? EXECUTION_GAS_CAP - intrinsicGas : 0n,
    fitsTransaction: estimatedTransactionGas <= EXECUTION_GAS_CAP,
  };
}

function parseLimit(value, name, { allowZero = false } = {}) {
  if (!/^[0-9]+$/.test(String(value))) throw new Error(`invalid ${name}: ${value}`);
  const n = BigInt(value);
  if (!allowZero && n === 0n) throw new Error(`${name} must be positive`);
  return n;
}

function parseByteLimit(value, name) {
  const n = parseLimit(value, name, { allowZero: true });
  if (n > BigInt(Number.MAX_SAFE_INTEGER)) throw new Error(`${name} exceeds safe integer range`);
  return Number(n);
}

module.exports = {
  CODE_SIZE_LIMIT, INITCODE_SIZE_LIMIT, EXECUTION_GAS_CAP,
  DEFAULT_MAX_BYTES, DEFAULT_GAS_LIMIT, MODEL,
  transactionBudget, parseLimit, parseByteLimit,
};

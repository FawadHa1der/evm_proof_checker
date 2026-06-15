// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.28;

interface ILeanKernel {
    function check(
        uint256[] calldata nameTab,
        bytes calldata nameStrs,
        uint256[] calldata levelTab,
        uint256[] calldata exprTab,
        uint256[] calldata pool,
        uint256[] calldata declTab
    ) external pure returns (uint8 verdict, uint64 failedDecl, uint16 reason);
}

/// @title  TheoremRegistry — persistent record of kernel-accepted exports
/// @notice Anyone can submit a (re-encoded) lean4export file. If the kernel
///         accepts it, the keccak hash of the full export is recorded, which
///         binds the *statements* (types) of every checked declaration:
///         anyone can later re-derive what was proven from the same data.
contract TheoremRegistry {
    ILeanKernel public immutable kernel;
    mapping(bytes32 => bool) public isChecked;

    event ExportChecked(bytes32 indexed exportHash, uint64 decls);

    constructor(address kernel_) {
        kernel = ILeanKernel(kernel_);
    }

    function exportHashOf(
        uint256[] calldata nameTab,
        bytes calldata nameStrs,
        uint256[] calldata levelTab,
        uint256[] calldata exprTab,
        uint256[] calldata pool,
        uint256[] calldata declTab
    ) public pure returns (bytes32) {
        return keccak256(abi.encode(nameTab, nameStrs, levelTab, exprTab, pool, declTab));
    }

    function submit(
        uint256[] calldata nameTab,
        bytes calldata nameStrs,
        uint256[] calldata levelTab,
        uint256[] calldata exprTab,
        uint256[] calldata pool,
        uint256[] calldata declTab
    ) external returns (uint8 verdict) {
        uint64 nDecls;
        (verdict, nDecls, ) = kernel.check(nameTab, nameStrs, levelTab, exprTab, pool, declTab);
        if (verdict == 0) {
            bytes32 h = exportHashOf(nameTab, nameStrs, levelTab, exprTab, pool, declTab);
            isChecked[h] = true;
            emit ExportChecked(h, nDecls);
        }
    }
}

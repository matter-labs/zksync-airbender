// SPDX-License-Identifier: MIT
pragma solidity =0.8.38;

interface SendProofVm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata value) external pure returns (bytes memory);
    function envAddress(string calldata name) external view returns (address);
    function startBroadcast() external;
    function stopBroadcast() external;
}

/// Used by send_proof.sh so the complete proof stays in a file rather than argv.
contract SendProof {
    SendProofVm constant vm = SendProofVm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function run() external {
        address verifier = vm.envAddress("VERIFIER_ADDR");
        bytes memory proof = vm.parseBytes(
            string.concat("0x", vm.readFile("@DATA@/single_tx_calldata.hex"))
        );
        vm.startBroadcast();
        (bool ok, bytes memory statement) = verifier.call(proof);
        vm.stopBroadcast();
        require(ok && statement.length == 64, "verification failed");
    }
}

// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

interface VmProofSender {
    function envAddress(string calldata name) external view returns (address);
    function envString(string calldata name) external view returns (string memory);
    function envUint(string calldata name) external view returns (uint256);
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata value) external pure returns (bytes memory);
    function startBroadcast(uint256 privateKey) external;
    function stopBroadcast() external;
}

/// Read calldata inside Foundry so even the largest WHIR proof never enters argv.
contract SendProofs {
    VmProofSender constant vm = VmProofSender(address(uint160(uint256(keccak256("hevm cheat code")))));
    event log_named_uint(string key, uint256 value);

    function run() external {
        bytes memory gkr = vm.parseBytes(string.concat("0x", vm.readFile(vm.envString("GKR_CALLDATA_PATH"))));
        bytes memory whir = vm.parseBytes(string.concat("0x", vm.readFile(vm.envString("WHIR_CALLDATA_PATH"))));
        address gkrVerifier = vm.envAddress("GKR_ADDR");
        address whirVerifier = vm.envAddress("WHIR_ADDR");
        require(gkrVerifier.code.length != 0 && whirVerifier.code.length != 0, "missing verifier code");
        emit log_named_uint("GKR calldata bytes", gkr.length);
        emit log_named_uint("WHIR calldata bytes", whir.length);
        vm.startBroadcast(vm.envUint("PROOF_SENDER_KEY"));
        (bool gkrOk,) = gkrVerifier.call(gkr);
        require(gkrOk, "GKR verification transaction reverted");
        (bool whirOk,) = whirVerifier.call(whir);
        require(whirOk, "WHIR verification transaction reverted");
        vm.stopBroadcast();
    }
}

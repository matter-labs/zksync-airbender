// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

import {GkrWhirRegistry} from "../src/GkrWhirRegistry.sol";

interface RegistryVm {
    function prank(address sender) external;
    function etch(address target, bytes calldata code) external;
    function expectRevert(bytes calldata reason) external;
}

contract RegistryFactory {
    function deploy(bytes memory initCode) external returns (GkrWhirRegistry) {
        address deployed;
        assembly {
            deployed := create2(0, add(initCode, 32), mload(initCode), 0)
        }
        require(deployed != address(0));
        return GkrWhirRegistry(deployed);
    }
}

contract RegistryBoundaryTest {
    RegistryVm constant vm = RegistryVm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant GKR = address(0x1001);
    address constant WHIR = address(0x1002);
    bytes32 constant KEY = bytes32(uint256(1));
    bytes32 constant OUTPUT = bytes32(uint256(2));
    bytes32 constant SETUP = bytes32(uint256(3));
    GkrWhirRegistry registry;

    function setUp() public {
        registry = new GkrWhirRegistry(address(this));
        vm.etch(GKR, hex"00");
        vm.etch(WHIR, hex"00");
    }

    function _gkr(bytes32 output, bytes32 setup) internal {
        vm.prank(GKR);
        registry.mark_gkr_verified(KEY, output, setup);
    }

    function _whir() internal {
        vm.prank(WHIR);
        registry.mark_whir_verified(KEY);
    }

    function test_uninitialized_registry_rejects_writes() public {
        vm.expectRevert(bytes("only GKR verifier"));
        _gkr(OUTPUT, SETUP);
        vm.expectRevert(bytes("only WHIR verifier"));
        _whir();
        require(registry.verificationMask(KEY) == GkrWhirRegistry.VerificationMask.None);
    }

    function test_only_initializer_can_register_pair() public {
        vm.expectRevert(bytes("only initializer"));
        vm.prank(address(0xbad));
        registry.initialize_verifiers(GKR, WHIR);
        registry.initialize_verifiers(GKR, WHIR);
        require(registry.gkrVerifier() == GKR && registry.whirVerifier() == WHIR);
        vm.expectRevert(bytes("already initialized"));
        registry.initialize_verifiers(WHIR, GKR);
    }

    function test_factory_deployment_preserves_explicit_initializer() public {
        registry = new RegistryFactory().deploy(
            abi.encodePacked(type(GkrWhirRegistry).creationCode, abi.encode(address(this)))
        );
        require(registry.initializer() == address(this));
        registry.initialize_verifiers(GKR, WHIR);
        _gkr(OUTPUT, SETUP);
        _whir();
        require(registry.verificationMask(KEY) == GkrWhirRegistry.VerificationMask.Both);
    }

    function test_invalid_authorities_are_rejected() public {
        vm.expectRevert(bytes("zero initializer"));
        new GkrWhirRegistry(address(0));
        vm.expectRevert(bytes("verifiers must differ"));
        registry.initialize_verifiers(GKR, GKR);
        vm.expectRevert(bytes("verifiers must be contracts"));
        registry.initialize_verifiers(address(0), WHIR);
        vm.expectRevert(bytes("verifiers must be contracts"));
        registry.initialize_verifiers(GKR, address(0xbad));
    }

    function test_unregistered_caller_cannot_record_pair() public {
        registry.initialize_verifiers(GKR, WHIR);
        vm.expectRevert(bytes("only GKR verifier"));
        registry.mark_gkr_verified(KEY, OUTPUT, SETUP);
        vm.expectRevert(bytes("only WHIR verifier"));
        registry.mark_whir_verified(KEY);
        require(registry.verificationMask(KEY) == GkrWhirRegistry.VerificationMask.None);
    }

    function test_verifier_roles_are_separate() public {
        registry.initialize_verifiers(GKR, WHIR);
        vm.expectRevert(bytes("only WHIR verifier"));
        vm.prank(GKR);
        registry.mark_whir_verified(KEY);
        vm.expectRevert(bytes("only GKR verifier"));
        vm.prank(WHIR);
        registry.mark_gkr_verified(KEY, OUTPUT, SETUP);
    }

    function test_pair_accepts_in_either_order_and_allows_identical_replays() public {
        registry.initialize_verifiers(GKR, WHIR);
        _gkr(OUTPUT, SETUP);
        require(registry.verificationMask(KEY) == GkrWhirRegistry.VerificationMask.Gkr);
        _whir();
        _gkr(OUTPUT, SETUP);
        _whir();
        require(registry.verificationMask(KEY) == GkrWhirRegistry.VerificationMask.Both);

        bytes32 other = bytes32(uint256(4));
        vm.prank(WHIR);
        registry.mark_whir_verified(other);
        require(registry.verificationMask(other) == GkrWhirRegistry.VerificationMask.Whir);
        vm.prank(GKR);
        registry.mark_gkr_verified(other, OUTPUT, SETUP);
        require(registry.verificationMask(other) == GkrWhirRegistry.VerificationMask.Both);
    }

    function test_public_data_cannot_change_before_or_after_acceptance() public {
        registry.initialize_verifiers(GKR, WHIR);
        _gkr(OUTPUT, SETUP);
        vm.expectRevert(bytes("conflicting public data"));
        _gkr(bytes32(0), SETUP);
        _whir();
        vm.expectRevert(bytes("conflicting public data"));
        _gkr(OUTPUT, bytes32(0));
        vm.expectRevert(bytes("only GKR verifier"));
        registry.mark_gkr_verified(KEY, bytes32(0), bytes32(0));
        (bytes32 output, bytes32 setup) = registry.commitmentPublicData(KEY);
        require(output == OUTPUT && setup == SETUP);
        require(registry.verificationMask(KEY) == GkrWhirRegistry.VerificationMask.Both);
    }
}

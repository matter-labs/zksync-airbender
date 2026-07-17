// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import {GkrFullVerifier} from "./GkrFullVerifier.sol";
interface Vm { function readFile(string calldata p) external view returns (string memory); function parseBytes(string calldata s) external pure returns (bytes memory); }
contract TT is GkrFullVerifier {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    event log_named_uint(string k,uint v); event log_named_bytes32(string k, bytes32 v);
    function _rd(string memory p) internal view returns (bytes memory) { return vm.parseBytes(string.concat("0x", vm.readFile(p))); }
    function test_c() external {
        bytes memory cd = _rd("../whir/testdata/gkr_full_calldata.hex");
        (bool ok, bytes memory ret) = address(this).call(cd); require(ok,"rv");
        uint fc; assembly{ fc:=mload(add(ret,128)) }
        emit log_named_uint("failCode",fc);
        { uint pcv; assembly{ pcv:=mload(add(ret,736)) } emit log_named_uint("final_pc",pcv); }
        bytes32 batching; bytes32 opening; bytes32 seedh; bytes32 pubv; bytes32 setupv; bytes32 commit;
        assembly {
            batching := mload(add(ret,768))
            opening  := mload(add(ret,800))
            seedh    := mload(add(ret,832))
            pubv     := mload(add(ret,864))
            setupv   := mload(add(ret,896))
            commit   := mload(add(ret,928))
        }
        emit log_named_bytes32("whir_batching", batching);
        emit log_named_bytes32("batched_opening", opening);
        emit log_named_bytes32("handoff_seed", seedh);
        emit log_named_bytes32("public_input", pubv);
        emit log_named_bytes32("setup_commitment", setupv);
        emit log_named_bytes32("commitment", commit);
    }
}

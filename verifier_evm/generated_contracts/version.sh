# Shared roots for the versioned verifier harnesses. Source after setting SCRIPT_DIR.
select_version() {
  case "$1" in
    2p21)
      CONTRACTS_ROOT=$SCRIPT_DIR/l1_wrap_2p21
      DATA_ROOT=$SCRIPT_DIR/../debug_data/l1_wrap_2p21
      REGISTRY_SALT=0x00000000000000000000000000000000000000000000000000616972621b0021
      VERIFIER_SALT=0x00000000000000000000000000000000000000000000000000616972621b0022
      # empty: deploy.sh deploys a TestRegistry first
      REGISTRY_ADDR=${REGISTRY_ADDR_2P21:-}
      ;;
    *) echo "expected verifier version 2p21, got: $1" >&2; exit 2 ;;
  esac
  AB_EVM_VERSION=$1
  export AB_EVM_VERSION
}

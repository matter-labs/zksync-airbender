# Shared roots for the versioned verifier harnesses. Source after setting SCRIPT_DIR.
select_version() {
  case "$1" in
    2p22)
      CONTRACTS_ROOT=$SCRIPT_DIR
      DATA_ROOT=$SCRIPT_DIR/../debug_data
      ;;
    2p21)
      CONTRACTS_ROOT=$SCRIPT_DIR/l1_wrap_2p21
      DATA_ROOT=$SCRIPT_DIR/../debug_data/l1_wrap_2p21
      ;;
    *) echo "expected verifier version 2p22 or 2p21, got: $1" >&2; exit 2 ;;
  esac
  AB_EVM_VERSION=$1
  export AB_EVM_VERSION
}

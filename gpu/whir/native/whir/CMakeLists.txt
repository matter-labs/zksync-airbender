target_sources(gpu_whir_native PRIVATE
        accumulate_eq.cu
        columns.cu
        fold.cu
        in_domain.cu
        leaves.cu
        residue_commit.cu
        proth120/base.cu
        proth120/commit.cu
        proth120/fold.cu
        proth120/round.cu
)

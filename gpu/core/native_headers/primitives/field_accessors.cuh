#pragma once

#include "memory.cuh"

#define AB_DEFINE_FIELD_ACCESSORS(F)                                                                                                                           \
  template <ld_modifier LD_MODIFIER = ld_modifier::none> struct F##_vector_getter : vector_getter<F, LD_MODIFIER> {};                                          \
                                                                                                                                                               \
  template <st_modifier ST_MODIFIER = st_modifier::none> struct F##_vector_setter : vector_setter<F, ST_MODIFIER> {};                                          \
                                                                                                                                                               \
  template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>                                                          \
  struct F##_vector_getter_setter : vector_getter_setter<F, LD_MODIFIER, ST_MODIFIER> {};                                                                      \
                                                                                                                                                               \
  template <ld_modifier LD_MODIFIER = ld_modifier::none> struct F##_matrix_getter : matrix_getter<F, LD_MODIFIER> {                                            \
    explicit F##_matrix_getter(size_t stride) : matrix_getter<F, LD_MODIFIER>(stride) {}                                                                       \
  };                                                                                                                                                           \
                                                                                                                                                               \
  template <st_modifier ST_MODIFIER = st_modifier::none> struct F##_matrix_setter : matrix_setter<F, ST_MODIFIER> {                                            \
    explicit F##_matrix_setter(size_t stride) : matrix_setter<F, ST_MODIFIER>(stride) {}                                                                       \
  };                                                                                                                                                           \
                                                                                                                                                               \
  template <ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>                                                          \
  struct F##_matrix_getter_setter : matrix_getter_setter<F, LD_MODIFIER, ST_MODIFIER> {                                                                        \
    explicit F##_matrix_getter_setter(size_t stride) : matrix_getter_setter<F, LD_MODIFIER, ST_MODIFIER>(stride) {}                                            \
  };

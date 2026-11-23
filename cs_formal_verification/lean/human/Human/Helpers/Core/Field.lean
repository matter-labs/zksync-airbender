module

@[expose] public section
namespace Airbender

/-- BabyBear prime. The current layout format carries no field identifier. -/
def babyBearModulus : Nat := 2013265921

/-- `2^-32 mod babyBearModulus`: field values are kept in Montgomery form (`x` held as `x · 2^32`), as Airbender's
    field code does (`field/src/baby_bear/base.rs`). -/
def montgomeryInverse : Nat := 943718400

end Airbender

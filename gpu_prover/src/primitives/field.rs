use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext2::BabyBearExt2;
use field::baby_bear::ext4::BabyBearExt4;
use field::baby_bear::ext6::BabyBearExt6;

pub(crate) type BaseField = BabyBearField;
pub(crate) type Ext2Field = BabyBearExt2;
pub(crate) type Ext4Field = BabyBearExt4;
pub(crate) type Ext6Field = BabyBearExt6;

pub(crate) type BF = BaseField;
pub(crate) type E2 = Ext2Field;
pub(crate) type E4 = Ext4Field;
pub(crate) type E6 = Ext6Field;

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext2::BabyBearExt2;
use field::baby_bear::ext4::BabyBearExt4;
use field::baby_bear::ext6::BabyBearExt6;

pub type BaseField = BabyBearField;
pub type Ext2Field = BabyBearExt2;
pub type Ext4Field = BabyBearExt4;
pub type Ext6Field = BabyBearExt6;

pub type BF = BaseField;
pub type E2 = Ext2Field;
pub type E4 = Ext4Field;
pub type E6 = Ext6Field;

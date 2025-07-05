pub trait FromBytes: Sized {
    fn from_le_bytes(bytes: &[u8]) -> Self;
    fn from_be_bytes(bytes: &[u8]) -> Self;
}

macro_rules! impl_from_bytes {
    ($t:ty) => {
        impl FromBytes for $t {
            fn from_le_bytes(bytes: &[u8]) -> Self {
                let mut array = [0u8; size_of::<$t>()];
                array.copy_from_slice(&bytes[..size_of::<$t>()]);
                <$t>::from_le_bytes(array)
            }

            fn from_be_bytes(bytes: &[u8]) -> Self {
                let mut array = [0u8; size_of::<$t>()];
                array.copy_from_slice(&bytes[..size_of::<$t>()]);
                <$t>::from_be_bytes(array)
            }
        }
    };
}

// Integers
impl_from_bytes!(u8);
impl_from_bytes!(u16);
impl_from_bytes!(u32);
impl_from_bytes!(u64);
impl_from_bytes!(u128);
impl_from_bytes!(i8);
impl_from_bytes!(i16);
impl_from_bytes!(i32);
impl_from_bytes!(i64);
impl_from_bytes!(i128);

// Floats
impl_from_bytes!(f32);
impl_from_bytes!(f64);

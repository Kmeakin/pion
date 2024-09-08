macro_rules! define_prims {
    ($name:ident { $($variant:ident = $value:literal $(,)?),* }) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub enum $name {
            $($variant),*
        }

        impl std::str::FromStr for $name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($value => Ok(Self::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl $name {
            pub fn name(&self) -> &'static str {
                match self {
                    $(Self::$variant => $value,)*
                }
            }
        }
    };
}

define_prims!(PrimVar {
    Type = "Type",
    Bool = "Bool",
    Int = "Int",
    Char = "Char",
    String = "String",
});

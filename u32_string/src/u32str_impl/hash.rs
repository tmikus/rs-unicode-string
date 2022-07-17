use std::hash::{Hash, Hasher};

impl Hash for super::u32str {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // TODO: Optimise this...
        for c in self.chars() {
            state.write_u32(*c as u32);
        }
    }
}

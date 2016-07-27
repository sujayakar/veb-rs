use std::collections::{Bound, BTreeSet, HashMap};

const LEAF_BITS: u8 = 8;

#[derive(Debug)]
enum VanEmdeBoas {
    Node(VanEmdeBoasNode),
    Leaf(VanEmdeBoasLeaf),
}

#[derive(Debug)]
struct VanEmdeBoasNode {
    keylen: u8,

    min: Option<u64>,
    max: Option<u64>,
    len: usize,

    summary: Box<VanEmdeBoas>,
    children: HashMap<u64, VanEmdeBoas>,
}

#[derive(Debug)]
struct VanEmdeBoasLeaf {
    keylen: u8,
    set: BTreeSet<u64>,
}

fn suffix_mask(num_bits: u8) -> u64 {
    assert!(num_bits < 64);
    (1 << num_bits) - 1
}

impl VanEmdeBoas {
    pub fn new() -> Self {
        VanEmdeBoas::create(64)
    }

    fn create(keylen: u8) -> Self {
        assert!(keylen <= 64);
        assert_eq!(keylen & (keylen - 1), 0);
        if keylen <= LEAF_BITS {
            VanEmdeBoas::Leaf(VanEmdeBoasLeaf {
                keylen: keylen,
                set: BTreeSet::new(),
            })
        } else {
            let childbits = keylen / 2;
            VanEmdeBoas::Node(VanEmdeBoasNode {
                keylen: keylen,

                min: None,
                max: None,
                len: 0,

                summary: Box::new(VanEmdeBoas::create(childbits)),
                children: HashMap::new(),
            })
        }
    }

    fn keylen(&self) -> u8 {
        match self {
            &VanEmdeBoas::Node(ref node) => node.keylen,
            &VanEmdeBoas::Leaf(ref leaf) => leaf.keylen,
        }
    }

    fn validate_key(&self, k: u64) {
        if self.keylen() == 64 {
            return;
        }
        assert_eq!(k >> self.keylen(), 0);
    }

    pub fn insert(&mut self, k: u64) {
        self.validate_key(k);
        match self {
            &mut VanEmdeBoas::Node(ref mut node) => node.insert(k),
            &mut VanEmdeBoas::Leaf(ref mut leaf) => {
                leaf.set.insert(k);
            },
        }
    }

    pub fn length(&self) -> usize {
        match self {
            &VanEmdeBoas::Node(ref node) => node.len,
            &VanEmdeBoas::Leaf(ref leaf) => leaf.set.len(),
        }
    }

    pub fn lookup(&self, k: u64) -> bool {
        self.validate_key(k);
        match self {
            &VanEmdeBoas::Node(ref node) => node.lookup(k),
            &VanEmdeBoas::Leaf(ref leaf) => leaf.set.contains(&k),
        }
    }

    pub fn min(&self) -> Option<u64> {
        match self {
            &VanEmdeBoas::Node(ref node) => node.min.or(node.max),
            &VanEmdeBoas::Leaf(ref leaf) => leaf.set.iter().next().cloned(),
        }
    }

    pub fn max(&self) -> Option<u64> {
        match self {
            &VanEmdeBoas::Node(ref node) => node.max.or(node.min),
            &VanEmdeBoas::Leaf(ref leaf) => leaf.set.iter().next_back().cloned(),
        }
    }

    pub fn successor(&self, k: u64) -> Option<u64> {
        self.validate_key(k);
        match self {
            &VanEmdeBoas::Node(ref node) => node.successor(k),
            &VanEmdeBoas::Leaf(ref leaf) => {
                leaf.set.range(Bound::Excluded(&k), Bound::Unbounded).next().cloned()
            }
        }
    }

    pub fn predecessor(&self, k: u64) -> Option<u64> {
        self.validate_key(k);
        match self {
            &VanEmdeBoas::Node(ref node) => node.predecessor(k),
            &VanEmdeBoas::Leaf(ref leaf) => {
                leaf.set.range(Bound::Unbounded, Bound::Excluded(&k))
                    .next_back()
                    .cloned()
            }
        }
    }
}

impl VanEmdeBoasNode {
    fn insert(&mut self, k: u64) {
        // Case 1: check to see if k is less than our min
        if let Some(min) = self.min.take() {
            if k == min {
                return;
            }
            else if k < min {
                self.min = Some(k);
                self.len += 1;
                self.insert(min);
                return;
            }
            else {
                self.min = Some(min);
            }
        }
        // Nothing there?  Consider ourselves done.
        else {
            self.min = Some(k);
            self.len += 1;
            return;
        }

        // Case 2: do the same for the max cell
        if let Some(max) = self.max.take() {
            if k == max {
                return;
            }
            else if k > max {
                self.max = Some(k);
                self.len += 1;
                self.insert(max);
                return;
            }
            else {
                self.max = Some(max);
            }
        } else {
            self.max = Some(k);
            self.len += 1;
            return;
        }

        // Okay, by now we're sure `min < k < max`
        let childbits = self.keylen / 2;
        let k_prefix = k >> childbits;
        let k_suffix = k & suffix_mask(childbits);
        let child = self.children.entry(k_prefix)
            .or_insert_with(|| VanEmdeBoas::create(childbits));

        if child.length() == 0 {
            self.summary.insert(k_prefix);
        }
        child.insert(k_suffix);
        self.len += 1;
    }

    fn lookup(&self, k: u64) -> bool {
        // Short circuit if empty
        if self.len == 0 {
            return false;
        }
        // Short circuit if k <= min
        if let Some(min) = self.min {
            if k < min {
                return false;
            }
            else if k == min {
                return true;
            }
        }
        // Do the same for max
        if let Some(max) = self.max {
            if max < k {
                return false;
            }
            else if max == k {
                return true;
            }
        }
        // We have to recurse, find out where
        let childbits = self.keylen / 2;
        let k_prefix = k >> childbits;
        let k_suffix = k & suffix_mask(childbits);
        if !self.summary.lookup(k_prefix) {
            return false;
        }
        self.children[&k_prefix].lookup(k_suffix)
    }

    fn successor(&self, k: u64) -> Option<u64> {
        match (self.min, self.max) {
            (None, None) => {
                return None;
            },
            (Some(min), _) if k < min => {
                return Some(min);
            },
            (_, Some(max)) if k >= max => {
                return None;
            },
            _ => (),
        }
        let childbits = self.keylen / 2;
        let k_prefix = k >> childbits;
        let k_suffix = k & suffix_mask(childbits);

        // First try to find a successor in `k`'s child
        if self.summary.lookup(k_prefix) {
            if let Some(r_suffix) = self.children[&k_prefix].successor(k_suffix) {
                return Some((k_prefix << childbits) | r_suffix);
            }
        }
        // Next, try the next child
        if let Some(next_prefix) = self.summary.successor(k_prefix) {
            let r_suffix = self.children[&next_prefix].min().unwrap();
            return Some((next_prefix << childbits) | r_suffix);
        }

        // We already checked that `k < max`
        self.max.clone()
    }

    fn predecessor(&self, k: u64) -> Option<u64> {
        match (self.min, self.max) {
            (None, None) => {
                return None;
            },
            (Some(min), _) if k <= min => {
                return None;
            },
            (_, Some(max)) if k > max => {
                return Some(max);
            },
            _ => (),
        }
        let childbits = self.keylen / 2;
        let k_prefix = k >> childbits;
        let k_suffix = k & suffix_mask(childbits);

        if self.summary.lookup(k_prefix) {
            if let Some(r_suffix) = self.children[&k_prefix].predecessor(k_suffix) {
                return Some((k_prefix << childbits) | r_suffix);
            }
        }
        if let Some(prev_prefix) = self.summary.predecessor(k_prefix) {
            let r_suffix = self.children[&prev_prefix].max().unwrap();
            return Some((prev_prefix << childbits) | r_suffix);
        }

        self.min.clone()
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeSet;
    use super::VanEmdeBoas;
    use rand;

    #[test]
    fn test_interface() {
        let mut s = VanEmdeBoas::new();
        assert_eq!(s.min(), None);
        assert_eq!(s.max(), None);
        assert_eq!(s.successor(0), None);
        assert_eq!(s.predecessor(1 << 32), None);

        s.insert(1);
        assert_eq!(s.min(), Some(1));
        assert_eq!(s.max(), Some(1));
        assert_eq!(s.successor(0), Some(1));
        assert_eq!(s.successor(1), None);
        assert_eq!(s.predecessor(1), None);
        assert_eq!(s.predecessor(2), Some(1));

        let different_child = (1u64 << 33) - 1;
        s.insert(different_child);
        assert_eq!(s.min(), Some(1));
        assert_eq!(s.max(), Some(different_child));
        assert_eq!(s.successor(0), Some(1));
        assert_eq!(s.successor(1), Some(different_child));
        assert_eq!(s.predecessor(1), None);
        assert_eq!(s.predecessor(different_child), Some(1));
        assert_eq!(s.predecessor(different_child + 1), Some(different_child));
    }

    #[test]
    fn test_iter_forwards() {
        for _ in 0..10 {
            let mut bt = BTreeSet::new();
            let mut ve = VanEmdeBoas::new();

            for _ in 0..1000 {
                let k: u64 = rand::random();
                bt.insert(k);
                ve.insert(k);
            }

            let btv: Vec<_> = bt.iter().cloned().collect();
            let mut cur = ve.min().unwrap();
            let mut vev = vec![cur];
            while let Some(next) = ve.successor(cur) {
                vev.push(next);
                cur = next;
            }
            assert_eq!(btv, vev);

            let btv: Vec<_> = bt.iter().rev().cloned().collect();
            let mut cur = ve.max().unwrap();
            let mut vev = vec![cur];
            while let Some(next) = ve.predecessor(cur) {
                vev.push(next);
                cur = next;
            }
            assert_eq!(btv, vev);
        }
    }

    #[test]
    fn test_iter_backwards() {
        for _ in 0..10 {
            let mut bt = BTreeSet::new();
            let mut ve = VanEmdeBoas::new();

            for _ in 0..1000 {
                let k: u64 = rand::random();
                bt.insert(k);
                ve.insert(k);
            }

            let btv: Vec<_> = bt.iter().rev().cloned().collect();
            let mut cur = ve.max().unwrap();
            let mut vev = vec![cur];
            while let Some(next) = ve.predecessor(cur) {
                vev.push(next);
                cur = next;
            }
            assert_eq!(btv, vev);
        }
    }
}

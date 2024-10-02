use std::{
    ops::{Deref, DerefMut},
    sync::{Arc, Mutex},
};

use either::Either;
use fractional_index::FractionalIndex;
use fxhash::FxHashMap;
use loro_common::{IdLp, TreeID};

use super::{FractionalIndexGenResult, TreeParentId};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NodePosition {
    pub(crate) position: FractionalIndex,
    // different nodes created by a peer may have the same position
    // when we merge updates that cause cycles.
    // for example [::fuzz::test::test_tree::same_peer_have_same_position()]
    pub(crate) idlp: IdLp,
}
#[derive(Debug, Clone)]
pub(crate) enum NodeChildren {
    Vec(Vec<(NodePosition, TreeID)>),
    BTree(btree::ChildTree),
}

impl Default for NodeChildren {
    fn default() -> Self {
        NodeChildren::Vec(vec![])
    }
}

impl NodeChildren {
    const MAX_SIZE_FOR_ARRAY: usize = 16;
    pub(super) fn get_index_by_child_id(&self, target: &TreeID) -> Option<usize> {
        match self {
            NodeChildren::Vec(v) => v.iter().position(|(_, id)| id == target),
            NodeChildren::BTree(btree) => btree.id_to_index(target),
        }
    }

    pub(super) fn get_last_insert_index_by_position(
        &self,
        node_position: &NodePosition,
    ) -> Result<usize, usize> {
        match self {
            NodeChildren::Vec(v) => v.binary_search_by_key(&node_position, |x| &x.0),
            NodeChildren::BTree(btree) => btree.get_index_by_node_position(node_position),
        }
    }

    fn get_node_position_at(&self, pos: usize) -> Option<&NodePosition> {
        match self {
            NodeChildren::Vec(v) => v.get(pos).map(|x| &x.0),
            NodeChildren::BTree(btree) => btree.get_elem_at(pos).map(|x| x.pos.as_ref()),
        }
    }

    fn get_elem_at(&self, pos: usize) -> Option<(&NodePosition, &TreeID)> {
        match self {
            NodeChildren::Vec(v) => v.get(pos).map(|x| (&x.0, &x.1)),
            NodeChildren::BTree(btree) => btree.get_elem_at(pos).map(|x| (x.pos.as_ref(), &x.id)),
        }
    }

    pub(super) fn generate_fi_at(&self, pos: usize, target: &TreeID) -> FractionalIndexGenResult {
        let mut reset_ids = vec![];
        let mut left = None;
        let mut next_right = None;
        {
            let mut right = None;
            let children_num = self.len();
            if children_num == 0 {
                return FractionalIndexGenResult::Ok(FractionalIndex::default());
            }

            if pos > 0 {
                left = self.get_node_position_at(pos - 1);
            }
            if pos < children_num {
                right = self.get_elem_at(pos);
            }

            let left_fi = left.map(|x| &x.position);
            // if left and right have the same fractional indexes, we need to scan further to
            // find all the ids that need to be reset
            if let Some(left_fi) = left_fi {
                if Some(left_fi) == right.map(|x| &x.0.position) {
                    // TODO: the min length between left and right
                    reset_ids.push(*right.unwrap().1);
                    for i in (pos + 1)..children_num {
                        let this_position =
                            self.get_node_position_at(i).map(|x| &x.position).unwrap();
                        if this_position == left_fi {
                            reset_ids.push(*self.get_elem_at(i).unwrap().1);
                        } else {
                            next_right = Some(this_position.clone());
                            break;
                        }
                    }
                }
            }

            if reset_ids.is_empty() {
                return FractionalIndexGenResult::Ok(
                    FractionalIndex::new(left.map(|x| &x.position), right.map(|x| &x.0.position))
                        .unwrap(),
                );
            }
        }
        let positions = FractionalIndex::generate_n_evenly(
            left.map(|x| &x.position),
            next_right.as_ref(),
            reset_ids.len() + 1,
        )
        .unwrap();
        FractionalIndexGenResult::Rearrange(
            Some(*target)
                .into_iter()
                .chain(reset_ids)
                .zip(positions)
                .collect(),
        )
    }

    pub(super) fn get_id_at(&self, pos: usize) -> Option<TreeID> {
        match self {
            NodeChildren::Vec(v) => v.get(pos).map(|x| x.1),
            NodeChildren::BTree(btree) => btree.get_elem_at(pos).map(|x| x.id),
        }
    }

    pub(super) fn delete_child(&mut self, target: &TreeID) {
        match self {
            NodeChildren::Vec(v) => {
                v.retain(|(_, id)| id != target);
            }
            NodeChildren::BTree(v) => {
                v.delete_child(target);
            }
        }
    }

    fn upgrade(&mut self) {
        match self {
            NodeChildren::Vec(v) => {
                let mut btree = btree::ChildTree::new();
                for (pos, id) in v.drain(..) {
                    btree.insert_child(pos, id);
                }
                *self = NodeChildren::BTree(btree);
            }
            NodeChildren::BTree(_) => unreachable!(),
        }
    }

    pub(super) fn insert_child(&mut self, pos: NodePosition, id: TreeID) {
        match self {
            NodeChildren::Vec(v) => {
                if v.len() >= Self::MAX_SIZE_FOR_ARRAY {
                    self.upgrade();
                    return self.insert_child(pos, id);
                }

                let r = v.binary_search_by(|(target, _)| target.cmp(&pos));
                match r {
                    Ok(_) => unreachable!(),
                    Err(i) => {
                        v.insert(i, (pos, id));
                    }
                }
            }
            NodeChildren::BTree(v) => {
                v.insert_child(pos, id);
            }
        }
    }

    pub(super) fn push_child_in_order(&mut self, pos: NodePosition, id: TreeID) {
        match self {
            NodeChildren::Vec(v) => {
                if v.len() >= Self::MAX_SIZE_FOR_ARRAY {
                    self.upgrade();
                    return self.push_child_in_order(pos, id);
                }

                if let Some(last) = v.last() {
                    assert!(last.0 < pos);
                }
                v.push((pos, id));
            }
            NodeChildren::BTree(v) => {
                v.push_child_in_order(pos, id);
            }
        }
    }

    pub(super) fn len(&self) -> usize {
        match self {
            NodeChildren::Vec(v) => v.len(),
            NodeChildren::BTree(v) => v.len(),
        }
    }

    pub(super) fn has_child(&self, node_position: &NodePosition) -> bool {
        match self {
            NodeChildren::Vec(v) => v
                .binary_search_by(|(target, _)| target.cmp(node_position))
                .is_ok(),
            NodeChildren::BTree(v) => v.has_child(node_position),
        }
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = (&NodePosition, &TreeID)> {
        match self {
            NodeChildren::Vec(v) => Either::Left(v.iter().map(|x| (&x.0, &x.1))),
            NodeChildren::BTree(t) => Either::Right(t.iter()),
        }
    }
}

#[derive(Clone, Default)]
pub(crate) struct TreeChildrenCache(pub(crate) Arc<Mutex<FxHashMap<TreeParentId, NodeChildren>>>);

impl TreeChildrenCache {
    pub fn with_cache(&self, f: impl FnOnce(&FxHashMap<TreeParentId, NodeChildren>)) {
        let t = self.0.try_lock().unwrap();
        f(&t)
    }

    pub fn with_cache_mut(&self, f: impl FnOnce(&mut FxHashMap<TreeParentId, NodeChildren>)) {
        let mut t = self.0.try_lock().unwrap();
        f(&mut t)
    }
}

mod btree {
    use std::{cmp::Ordering, ops::Range, sync::Arc};

    use fxhash::FxHashMap;
    use generic_btree::{
        rle::{CanRemove, HasLength, Mergeable, Sliceable, TryInsert},
        BTree, BTreeTrait, Cursor, FindResult, LeafIndex, LengthFinder, Query, UseLengthFinder,
    };
    use loro_common::TreeID;

    use super::NodePosition;

    struct ChildTreeTrait;
    #[derive(Debug, Clone)]
    pub(crate) struct ChildTree {
        tree: BTree<ChildTreeTrait>,
        id_to_leaf_index: FxHashMap<TreeID, LeafIndex>,
    }

    impl ChildTree {
        pub(super) fn new() -> Self {
            Self {
                tree: BTree::new(),
                id_to_leaf_index: FxHashMap::default(),
            }
        }

        pub(super) fn insert_child(&mut self, pos: NodePosition, id: TreeID) {
            let (c, _) = self.tree.insert::<KeyQuery>(
                &pos,
                Elem {
                    pos: Arc::new(pos.clone()),
                    id,
                },
            );

            self.id_to_leaf_index.insert(id, c.leaf);
        }

        pub(super) fn push_child_in_order(&mut self, pos: NodePosition, id: TreeID) {
            let c = self.tree.push(Elem {
                pos: Arc::new(pos.clone()),
                id,
            });
            self.id_to_leaf_index.insert(id, c.leaf);
        }

        pub(super) fn delete_child(&mut self, id: &TreeID) {
            if let Some(leaf) = self.id_to_leaf_index.remove(id) {
                self.tree.remove_leaf(Cursor { leaf, offset: 0 });
            } else {
                panic!("The id is not in the tree");
            }
        }

        pub(super) fn has_child(&self, pos: &NodePosition) -> bool {
            match self.tree.query::<KeyQuery>(pos) {
                Some(r) => r.found,
                None => false,
            }
        }

        pub(super) fn iter(&self) -> impl Iterator<Item = (&NodePosition, &TreeID)> {
            self.tree.iter().map(|x| (&*x.pos, &x.id))
        }

        pub(super) fn len(&self) -> usize {
            self.tree.root_cache().len
        }

        pub(super) fn get_elem_at(&self, pos: usize) -> Option<&Elem> {
            let result = self.tree.query::<LengthFinder>(&pos)?;
            if !result.found {
                return None;
            }
            self.tree.get_elem(result.leaf())
        }

        pub(super) fn id_to_index(&self, id: &TreeID) -> Option<usize> {
            let leaf_index = self.id_to_leaf_index.get(id)?;
            let mut ans = 0;
            self.tree.visit_previous_caches(
                Cursor {
                    leaf: *leaf_index,
                    offset: 0,
                },
                |prev| match prev {
                    generic_btree::PreviousCache::NodeCache(c) => {
                        ans += c.len;
                    }
                    generic_btree::PreviousCache::PrevSiblingElem(_) => {
                        ans += 1;
                    }
                    generic_btree::PreviousCache::ThisElemAndOffset { .. } => {}
                },
            );

            Some(ans)
        }

        pub(super) fn get_index_by_node_position(
            &self,
            node_position: &NodePosition,
        ) -> Result<usize, usize> {
            let Some(res) = self.tree.query::<KeyQuery>(node_position) else {
                return Ok(0);
            };
            let mut ans = 0;
            self.tree
                .visit_previous_caches(res.cursor, |prev| match prev {
                    generic_btree::PreviousCache::NodeCache(c) => {
                        ans += c.len;
                    }
                    generic_btree::PreviousCache::PrevSiblingElem(_) => {
                        ans += 1;
                    }
                    generic_btree::PreviousCache::ThisElemAndOffset { elem: _, offset } => {
                        ans += offset;
                    }
                });
            if res.found {
                Ok(ans)
            } else {
                Err(ans)
            }
        }
    }

    #[derive(Clone, Debug)]
    pub(super) struct Elem {
        pub(super) pos: Arc<NodePosition>,
        pub(super) id: TreeID,
    }

    impl Mergeable for Elem {
        fn can_merge(&self, _rhs: &Self) -> bool {
            false
        }

        fn merge_right(&mut self, _rhs: &Self) {
            unreachable!()
        }

        fn merge_left(&mut self, _left: &Self) {
            unreachable!()
        }
    }

    impl HasLength for Elem {
        fn rle_len(&self) -> usize {
            1
        }
    }

    impl Sliceable for Elem {
        fn _slice(&self, range: std::ops::Range<usize>) -> Self {
            assert!(range.len() == 1);
            self.clone()
        }
    }

    impl CanRemove for Elem {
        fn can_remove(&self) -> bool {
            false
        }
    }

    impl TryInsert for Elem {
        fn try_insert(&mut self, _pos: usize, elem: Self) -> Result<(), Self>
        where
            Self: Sized,
        {
            Err(elem)
        }
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    struct Cache {
        range: Option<Range<Arc<NodePosition>>>,
        len: usize,
    }

    impl BTreeTrait for ChildTreeTrait {
        type Elem = Elem;
        type Cache = Cache;
        type CacheDiff = ();
        const USE_DIFF: bool = false;

        fn calc_cache_internal(
            cache: &mut Self::Cache,
            caches: &[generic_btree::Child<Self>],
        ) -> Self::CacheDiff {
            if caches.is_empty() {
                *cache = Default::default();
                return;
            }

            *cache = Cache {
                range: Some(
                    caches[0].cache.range.as_ref().unwrap().start.clone()
                        ..caches
                            .last()
                            .unwrap()
                            .cache
                            .range
                            .as_ref()
                            .unwrap()
                            .end
                            .clone(),
                ),
                len: caches.iter().map(|x| x.cache.len).sum(),
            };
        }

        fn apply_cache_diff(_cache: &mut Self::Cache, _diff: &Self::CacheDiff) {
            unreachable!()
        }

        fn merge_cache_diff(_diff1: &mut Self::CacheDiff, _diff2: &Self::CacheDiff) {}

        fn get_elem_cache(elem: &Self::Elem) -> Self::Cache {
            Cache {
                range: Some(elem.pos.clone()..elem.pos.clone()),
                len: 1,
            }
        }

        fn new_cache_to_diff(_cache: &Self::Cache) -> Self::CacheDiff {}

        fn sub_cache(_cache_lhs: &Self::Cache, _cache_rhs: &Self::Cache) -> Self::CacheDiff {}
    }

    struct KeyQuery;

    impl Query<ChildTreeTrait> for KeyQuery {
        type QueryArg = NodePosition;

        #[inline(always)]
        fn init(_target: &Self::QueryArg) -> Self {
            KeyQuery
        }

        #[inline]
        fn find_node(
            &mut self,
            target: &Self::QueryArg,
            caches: &[generic_btree::Child<ChildTreeTrait>],
        ) -> FindResult {
            let result = caches.binary_search_by(|x| {
                let range = x.cache.range.as_ref().unwrap();
                if target < &range.start {
                    core::cmp::Ordering::Greater
                } else if target > &range.end {
                    core::cmp::Ordering::Less
                } else {
                    core::cmp::Ordering::Equal
                }
            });

            match result {
                Ok(i) => FindResult::new_found(i, 0),
                Err(i) => FindResult::new_missing(
                    i.min(caches.len() - 1),
                    if i == caches.len() { 1 } else { 0 },
                ),
            }
        }

        #[inline(always)]
        fn confirm_elem(
            &mut self,
            q: &Self::QueryArg,
            elem: &<ChildTreeTrait as BTreeTrait>::Elem,
        ) -> (usize, bool) {
            match q.cmp(&elem.pos) {
                Ordering::Less => (0, false),
                Ordering::Equal => (0, true),
                Ordering::Greater => (1, false),
            }
        }
    }

    impl UseLengthFinder<ChildTreeTrait> for ChildTreeTrait {
        fn get_len(cache: &<ChildTreeTrait as BTreeTrait>::Cache) -> usize {
            cache.len
        }
    }
}

impl std::fmt::Debug for TreeChildrenCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "TreeChildrenCache {{")?;
        for (parent, children) in self.0.try_lock().unwrap().iter() {
            writeln!(f, "  {:?}:{{", parent)?;
            for (position, id) in children.iter() {
                writeln!(f, "      {:?} -> {:?}", position, id)?;
            }
            writeln!(f, "  }}")?;
        }
        writeln!(f, "}}")
    }
}

impl NodePosition {
    pub(super) fn new(position: FractionalIndex, idlp: IdLp) -> Self {
        Self { position, idlp }
    }
}

mod jitter {
    use super::{FractionalIndexGenResult, NodeChildren};
    use fractional_index::FractionalIndex;
    use loro_common::TreeID;
    use rand::Rng;

    impl NodeChildren {
        pub(crate) fn generate_fi_at_jitter(
            &self,
            pos: usize,
            target: &TreeID,
            rng: &mut impl Rng,
            jitter: u8,
        ) -> FractionalIndexGenResult {
            let mut reset_ids = vec![];
            let mut left = None;
            let mut next_right = None;
            {
                let mut right = None;
                let children_num = self.len();
                if children_num == 0 {
                    return FractionalIndexGenResult::Ok(FractionalIndex::jitter_default(
                        rng, jitter,
                    ));
                }

                if pos > 0 {
                    left = self.get_node_position_at(pos - 1);
                }
                if pos < children_num {
                    right = self.get_elem_at(pos);
                }

                let left_fi = left.map(|x| &x.position);
                // if left and right have the same fractional indexes, we need to scan further to
                // find all the ids that need to be reset
                if let Some(left_fi) = left_fi {
                    if Some(left_fi) == right.map(|x| &x.0.position) {
                        // TODO: the min length between left and right
                        reset_ids.push(*right.unwrap().1);
                        for i in (pos + 1)..children_num {
                            let this_position = &self.get_node_position_at(i).unwrap().position;
                            if this_position == left_fi {
                                reset_ids.push(*self.get_elem_at(i).unwrap().1);
                            } else {
                                next_right = Some(this_position.clone());
                                break;
                            }
                        }
                    }
                }

                if reset_ids.is_empty() {
                    return FractionalIndexGenResult::Ok(
                        FractionalIndex::new_jitter(
                            left.map(|x| &x.position),
                            right.map(|x| &x.0.position),
                            rng,
                            jitter,
                        )
                        .unwrap(),
                    );
                }
            }
            let positions = FractionalIndex::generate_n_evenly_jitter(
                left.map(|x| &x.position),
                next_right.as_ref(),
                reset_ids.len() + 1,
                rng,
                jitter,
            )
            .unwrap();
            FractionalIndexGenResult::Rearrange(
                Some(*target)
                    .into_iter()
                    .chain(reset_ids)
                    .zip(positions)
                    .collect(),
            )
        }
    }
}

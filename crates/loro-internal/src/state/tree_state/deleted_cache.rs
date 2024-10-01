use std::{collections::VecDeque, sync::Arc};

use enum_dispatch::enum_dispatch;
use fractional_index::FractionalIndex;
use fxhash::FxHashMap;
use loro_common::{IdFull, PeerID, TreeID};

use super::{NodePosition, TreeChildrenCache, TreeParentId, TreeStateNode};

#[enum_dispatch(ToDeleteNode)]
#[derive(Debug, Clone)]
pub enum DeletedNodes {
    Nodes(DeletedNodesInner),
    Cache(UnParsedDeletedNodes),
}
#[enum_dispatch]
pub trait ToDeleteNode {
    fn insert_delete_node_and_descendants(
        &mut self,
        target: TreeID,
        id: IdFull,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
        children: &mut TreeChildrenCache,
    );

    fn remove_from_deleted(&mut self, target: TreeID, children: &mut TreeChildrenCache);

    fn mov_in_deleted(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
        children: &mut TreeChildrenCache,
    );
}

#[derive(Debug, Clone)]
pub struct UnParsedDeletedNodes {
    peers: Arc<Vec<PeerID>>,
    bytes: Arc<Vec<u8>>,
    new_delete: DeletedNodesInner,
}

impl UnParsedDeletedNodes {
    fn parse(self) -> DeletedNodesInner {}
}

#[derive(Debug, Clone, Default)]
pub struct DeletedNodesInner {
    tree: FxHashMap<TreeID, TreeStateNode>,
}

impl ToDeleteNode for DeletedNodesInner {
    fn insert_delete_node_and_descendants(
        &mut self,
        target: TreeID,
        id: IdFull,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
        children: &mut TreeChildrenCache,
    ) {
        if let Some(old_parent) = tree.get(&target).map(|x| x.parent) {
            // remove old position
            if let Some(x) = children.get_mut(&old_parent) {
                x.delete_child(&target);
            }
        }
        tree.remove(&target).unwrap();
        self.tree.insert(
            target,
            TreeStateNode {
                parent: TreeParentId::Deleted,
                position: None,
                last_move_op: id,
            },
        );
        children
            .entry(TreeParentId::Deleted)
            .or_default()
            .insert_child(
                NodePosition::new(FractionalIndex::default(), id.idlp()),
                target,
            );
        let mut q = VecDeque::from_iter(
            children
                .get(&TreeParentId::Node(target))
                .unwrap()
                .iter()
                .map(|n| *n.1),
        );
        while let Some(child) = q.pop_front() {
            let node = tree.remove(&child).unwrap();
            self.tree.insert(child, node);
            q.extend(
                children
                    .get(&TreeParentId::Node(child))
                    .unwrap()
                    .iter()
                    .map(|n| *n.1),
            );
        }
    }

    fn remove_from_deleted(&mut self, target: TreeID, children: &mut TreeChildrenCache) {}
    fn mov_in_deleted(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
        children: &mut TreeChildrenCache,
    ) {
    }
}

impl ToDeleteNode for UnParsedDeletedNodes {
    fn insert_delete_node_and_descendants(
        &mut self,
        target: TreeID,
        id: IdFull,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
        children_mapping: &mut TreeChildrenCache,
    ) {
        self.new_delete
            .insert_delete_node_and_descendants(target, id, tree, children_mapping);
    }

    fn remove_from_deleted(&mut self, target: TreeID, children: &mut TreeChildrenCache) {}
    fn mov_in_deleted(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
        children: &mut TreeChildrenCache,
    ) {
    }
}

use std::{collections::VecDeque, sync::Arc};

use fractional_index::FractionalIndex;
use fxhash::FxHashMap;
use itertools::Itertools;
use loro_common::{IdFull, Lamport, PeerID, TreeID};

use super::{snapshot::EncodedTree, NodePosition, TreeChildrenCache, TreeParentId, TreeStateNode};

#[derive(Debug, Clone)]
pub enum DeletedNodes {
    Nodes(DeletedNodesInner),
    Cache(UnParsedDeletedNodes),
}

pub trait ToDeleteNode {
    fn insert_delete_node_to_root(
        &mut self,
        target: TreeID,
        id: IdFull,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    );

    fn insert_delete_node_to_sub_tree(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    );

    fn remove_from_deleted(&mut self, target: TreeID);

    fn mov_in_deleted(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
    );

    fn all_deleted_nodes(&mut self) -> Vec<TreeStateNode>;
}

impl ToDeleteNode for DeletedNodes {
    fn insert_delete_node_to_root(
        &mut self,
        target: TreeID,
        id: IdFull,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    ) {
        match self {
            DeletedNodes::Cache(x) => x.new_delete.insert_delete_node_to_root(target, id, tree),
            DeletedNodes::Nodes(x) => x.insert_delete_node_to_root(target, id, tree),
        }
    }

    fn insert_delete_node_to_sub_tree(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    ) {
        match self {
            DeletedNodes::Cache(x) => {
                let this = std::mem::take(x);
                let mut deleted = this.parse();
                deleted.insert_delete_node_to_sub_tree(target, parent, id, position, tree);
                *self = DeletedNodes::Nodes(deleted);
            }
            DeletedNodes::Nodes(x) => {
                x.insert_delete_node_to_sub_tree(target, parent, id, position, tree)
            }
        }
    }

    fn remove_from_deleted(&mut self, target: TreeID) {
        match self {
            DeletedNodes::Cache(x) => {
                if x.new_delete.tree.contains_key(&target) {
                    x.new_delete.remove_from_deleted(target)
                } else {
                    let this = std::mem::take(x);
                    let mut deleted = this.parse();
                    deleted.remove_from_deleted(target);
                    *self = DeletedNodes::Nodes(deleted);
                }
            }
            DeletedNodes::Nodes(x) => x.remove_from_deleted(target),
        }
    }

    fn mov_in_deleted(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
    ) {
        match self {
            DeletedNodes::Cache(x) => {
                let this = std::mem::take(x);
                let mut deleted = this.parse();
                deleted.mov_in_deleted(target, parent, id, position);
                *self = DeletedNodes::Nodes(deleted);
            }
            DeletedNodes::Nodes(x) => x.mov_in_deleted(target, parent, id, position),
        }
    }

    fn all_deleted_nodes(&mut self) -> Vec<TreeStateNode> {
        match self {
            DeletedNodes::Cache(x) => {
                let this = std::mem::take(x);
                let deleted = this.parse();
                *self = DeletedNodes::Nodes(deleted);
                self.all_deleted_nodes()
            }
            DeletedNodes::Nodes(x) => x.all_deleted_nodes(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct UnParsedDeletedNodes {
    peers: Arc<Vec<PeerID>>,
    fractional_indexes: Arc<Vec<Vec<u8>>>,
    bytes: Arc<Vec<u8>>,
    new_delete: DeletedNodesInner,
}

impl UnParsedDeletedNodes {
    fn parse(self) -> DeletedNodesInner {
        let mut ans = DeletedNodesInner::default();
        let encoded_tree: EncodedTree = serde_columnar::from_bytes(&self.bytes).unwrap();
        let node_ids = encoded_tree
            .node_ids
            .iter()
            .map(|x| TreeID::new(self.peers[x.peer_idx], x.counter))
            .collect_vec();
        for (node_id, node) in node_ids.iter().zip(encoded_tree.nodes.into_iter()) {
            let parent = match node.parent_idx_plus_two {
                0 => TreeParentId::Root,
                1 => TreeParentId::Deleted,
                n => {
                    let id = node_ids[n - 2];
                    TreeParentId::from(Some(id))
                }
            };
            let position = FractionalIndex::from_bytes(
                self.fractional_indexes[node.fractional_index_idx].clone(),
            );
            let last_move_op = IdFull::new(
                self.peers[node.last_set_peer_idx],
                node.last_set_counter,
                (node.last_set_lamport_sub_counter + node.last_set_counter) as Lamport,
            );
            ans.tree.insert(
                *node_id,
                TreeStateNode {
                    parent,
                    position: position.clone(),
                    last_move_op,
                },
            );
            ans.children.with_cache_mut(move |children| {
                debug_assert!(!children.contains_key(&parent));
                let entry = children.entry(parent).or_default();
                let node_position = NodePosition::new(position, last_move_op.idlp());
                debug_assert!(!entry.has_child(&node_position));
                entry.push_child_in_order(node_position, *node_id);
            });
        }

        for (target, node) in self.new_delete.tree {
            debug_assert!(!ans.tree.contains_key(&target));
            ans.tree.insert(target, node);
        }

        ans
    }
}

#[derive(Debug, Clone, Default)]
pub struct DeletedNodesInner {
    tree: FxHashMap<TreeID, TreeStateNode>,
    children: TreeChildrenCache,
}

impl ToDeleteNode for DeletedNodesInner {
    fn insert_delete_node_to_root(
        &mut self,
        target: TreeID,
        id: IdFull,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    ) {
        self.insert_deleted_to_parent(
            target,
            id,
            TreeParentId::Deleted,
            FractionalIndex::default(),
            tree,
        );
    }

    fn insert_delete_node_to_sub_tree(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    ) {
        self.insert_deleted_to_parent(target, id, parent, position, tree);
    }

    fn remove_from_deleted(&mut self, target: TreeID) {
        let node = self.tree.remove(&target).unwrap();
        self.children
            .0
            .try_lock()
            .unwrap()
            .get_mut(&node.parent)
            .unwrap()
            .delete_child(&target);
    }

    fn mov_in_deleted(
        &mut self,
        target: TreeID,
        parent: TreeParentId,
        id: IdFull,
        position: FractionalIndex,
    ) {
        let node = self.tree.get_mut(&target).unwrap();
        let old_parent = node.parent;
        *node = TreeStateNode {
            parent,
            position: position.clone(),
            last_move_op: id,
        };
        self.children.with_cache_mut(|children| {
            children.get_mut(&old_parent).unwrap().delete_child(&target);
            children.entry(parent).or_default().insert_child(
                NodePosition {
                    position,
                    idlp: id.idlp(),
                },
                target,
            );
        });
    }

    fn all_deleted_nodes(&mut self) -> Vec<TreeStateNode> {
        self.tree.values().into_iter().cloned().collect()
    }
}

impl DeletedNodesInner {
    fn insert_deleted_to_parent(
        &mut self,
        target: TreeID,
        id: IdFull,
        parent: TreeParentId,
        position: FractionalIndex,
        tree: &mut FxHashMap<TreeID, TreeStateNode>,
    ) {
        println!("\n\n{tree:?}");
        if let Some(old_parent) = tree.get(&target).map(|x| x.parent) {
            // remove old position
            if let Some(x) = self.children.0.try_lock().unwrap().get_mut(&old_parent) {
                x.delete_child(&target);
            }
        }
        tree.remove(&target).unwrap();
        self.tree.insert(
            target,
            TreeStateNode {
                parent,
                position: position.clone(),
                last_move_op: id,
            },
        );

        println!(
            "children {:?} \n {parent:?} {target} {id:?}",
            self.children.0.try_lock().unwrap()
        );

        self.children.with_cache_mut(|children| {
            children
                .entry(parent)
                .or_default()
                .insert_child(NodePosition::new(position, id.idlp()), target);
            let mut q = VecDeque::from_iter(
                children
                    .entry(TreeParentId::Node(target))
                    .or_default()
                    .iter()
                    .map(|n| *n.1),
            );
            while let Some(child) = q.pop_front() {
                let node = tree.remove(&child).unwrap();
                self.tree.insert(child, node);
                q.extend(
                    children
                        .entry(TreeParentId::Node(child))
                        .or_default()
                        .iter()
                        .map(|n| *n.1),
                );
            }
        });
    }
}

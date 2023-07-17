use std::borrow::Cow;

use enum_as_inner::EnumAsInner;
use enum_dispatch::enum_dispatch;
use fxhash::{FxHashMap, FxHashSet};
use ring::rand::SystemRandom;

use crate::{
    configure::SecureRandomGenerator,
    container::{registry::ContainerIdx, ContainerIdRaw},
    event::Diff,
    id::{Counter, PeerID},
    op::RawOp,
    version::Frontiers,
    ContainerType, LoroValue,
};

mod list_state;
mod map_state;
mod text_state;

pub(crate) use list_state::ListState;
pub(crate) use map_state::MapState;
pub(crate) use text_state::TextState;

use super::{arena::SharedArena, oplog::OpLog};

#[derive(Clone)]
pub struct AppState {
    pub(super) peer: PeerID,
    pub(super) next_counter: Counter,

    pub(super) frontiers: Frontiers,
    pub(super) states: FxHashMap<ContainerIdx, State>,
    pub(super) arena: SharedArena,

    in_txn: bool,
    changed_in_txn: FxHashSet<ContainerIdx>,
}

#[enum_dispatch]
pub trait ContainerState: Clone {
    fn apply_diff(&mut self, diff: &Diff, arena: &SharedArena);
    fn apply_op(&mut self, op: RawOp);

    /// Start a transaction
    ///
    /// The transaction may be aborted later, then all the ops during this transaction need to be undone.
    fn start_txn(&mut self);
    fn abort_txn(&mut self);
    fn commit_txn(&mut self);

    fn get_value(&self) -> LoroValue;
}

#[allow(clippy::enum_variant_names)]
#[enum_dispatch(ContainerState)]
#[derive(EnumAsInner, Clone, Debug)]
pub enum State {
    ListState,
    MapState,
    TextState,
}

impl State {
    pub fn new_list() -> Self {
        Self::ListState(ListState::default())
    }

    pub fn new_map() -> Self {
        Self::MapState(MapState::new())
    }

    pub fn new_text() -> Self {
        Self::TextState(TextState::default())
    }
}

#[derive(Debug, Clone)]
pub struct ContainerStateDiff {
    pub idx: ContainerIdx,
    pub diff: Diff,
}

pub struct AppStateDiff<'a> {
    pub(crate) diff: Cow<'a, [ContainerStateDiff]>,
    pub(crate) frontiers: Cow<'a, Frontiers>,
}

impl AppState {
    pub fn new(oplog: &OpLog) -> Self {
        let peer = SystemRandom::new().next_u64();
        // TODO: maybe we should switch to certain version in oplog
        Self {
            peer,
            next_counter: 0,
            frontiers: Frontiers::default(),
            states: FxHashMap::default(),
            arena: oplog.arena.clone(),
            in_txn: false,
            changed_in_txn: FxHashSet::default(),
        }
    }

    pub fn new_from_arena(arena: SharedArena) -> Self {
        let peer = SystemRandom::new().next_u64();
        // TODO: maybe we should switch to certain version in oplog
        Self {
            peer,
            arena,
            next_counter: 0,
            frontiers: Frontiers::default(),
            states: FxHashMap::default(),
            in_txn: false,
            changed_in_txn: FxHashSet::default(),
        }
    }

    pub fn set_peer_id(&mut self, peer: PeerID) {
        self.peer = peer;
    }

    pub fn apply_diff(&mut self, AppStateDiff { diff, frontiers }: AppStateDiff) {
        if self.in_txn {
            panic!("apply_diff should not be called in a transaction");
        }

        for diff in diff.iter() {
            let state = self.states.entry(diff.idx).or_insert_with(|| {
                let id = self.arena.get_container_id(diff.idx).unwrap();
                create_state(id.container_type())
            });

            if self.in_txn {
                state.start_txn();
                self.changed_in_txn.insert(diff.idx);
            }

            state.apply_diff(&diff.diff, &self.arena);
        }

        self.frontiers = frontiers.into_owned();
    }

    pub fn apply_local_op(&mut self, op: RawOp) {
        let state = self.states.entry(op.container).or_insert_with(|| {
            let id = self.arena.get_container_id(op.container).unwrap();
            create_state(id.container_type())
        });

        if self.in_txn {
            state.start_txn();
            self.changed_in_txn.insert(op.container);
        }

        state.apply_op(op);
    }

    pub(crate) fn start_txn(&mut self) {
        self.in_txn = true;
    }

    pub(crate) fn abort_txn(&mut self) {
        for container_idx in std::mem::take(&mut self.changed_in_txn) {
            self.states.get_mut(&container_idx).unwrap().abort_txn();
        }

        self.in_txn = false;
    }

    pub(crate) fn commit_txn(&mut self, new_frontiers: Frontiers, next_counter: Counter) {
        for container_idx in std::mem::take(&mut self.changed_in_txn) {
            self.states.get_mut(&container_idx).unwrap().commit_txn();
        }

        self.in_txn = false;
        self.frontiers = new_frontiers;
        self.next_counter = next_counter;
    }

    pub(super) fn get_state_mut(&mut self, idx: ContainerIdx) -> Option<&mut State> {
        self.states.get_mut(&idx)
    }

    pub(super) fn get_state(&self, idx: ContainerIdx) -> Option<&State> {
        self.states.get(&idx)
    }

    pub(crate) fn get_value_by_idx(&self, container_idx: ContainerIdx) -> LoroValue {
        self.states
            .get(&container_idx)
            .map(|x| x.get_value())
            .unwrap_or(LoroValue::Null)
    }

    pub(super) fn set_state(&mut self, idx: ContainerIdx, state: State) {
        assert!(self.states.insert(idx, state).is_none(), "overiding states")
    }

    /// id can be a str, ContainerID, or ContainerIdRaw.
    /// if it's str it will use Root container, which will not be None
    pub fn get_text<I: Into<ContainerIdRaw>>(&mut self, id: I) -> Option<&text_state::TextState> {
        let id: ContainerIdRaw = id.into();
        let idx = match id {
            ContainerIdRaw::Root { name } => Some(self.arena.register_container(
                &crate::container::ContainerID::Root {
                    name,
                    container_type: crate::ContainerType::Text,
                },
            )),
            ContainerIdRaw::Normal { id: _ } => self
                .arena
                .id_to_idx(&id.with_type(crate::ContainerType::Text)),
        };

        let idx = idx.unwrap();
        self.states
            .entry(idx)
            .or_insert_with(State::new_text)
            .as_text_state()
    }

    pub(crate) fn with_state<F, R>(&self, idx: ContainerIdx, f: F) -> R
    where
        F: FnOnce(&State) -> R,
    {
        f(self.states.get(&idx).unwrap())
    }

    pub(super) fn is_in_txn(&self) -> bool {
        self.in_txn
    }

    pub fn is_empty(&self) -> bool {
        !self.in_txn && self.states.is_empty() && self.arena.is_empty()
    }
}

pub fn create_state(kind: ContainerType) -> State {
    match kind {
        ContainerType::Text => State::TextState(TextState::new()),
        ContainerType::Map => State::MapState(MapState::new()),
        ContainerType::List => State::ListState(ListState::new()),
    }
}

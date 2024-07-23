//! Experimental support for multiproofs.
use crate::{
    lib::*,
    merkleization::{
        generalized_index::{get_bit, get_path_length, parent, sibling},
        GeneralizedIndex, MerkleizationError as Error, Node,
    },
};
use sha2::{Digest, Sha256};

fn get_branch_indices(tree_index: GeneralizedIndex) -> Vec<GeneralizedIndex> {
    let mut focus = sibling(tree_index);
    let mut result = vec![focus];
    while focus > 1 {
        focus = sibling(parent(focus));
        result.push(focus);
    }
    result.truncate(result.len() - 1);
    result
}

fn get_path_indices(tree_index: GeneralizedIndex) -> Vec<GeneralizedIndex> {
    let mut focus = tree_index;
    let mut result = vec![focus];
    while focus > 1 {
        focus = parent(focus);
        result.push(focus);
    }
    result.truncate(result.len() - 1);
    result
}

fn get_helper_indices(indices: &[GeneralizedIndex]) -> Vec<GeneralizedIndex> {
    let mut all_helper_indices = HashSet::new();
    let mut all_path_indices = HashSet::new();

    for index in indices {
        all_helper_indices.extend(get_branch_indices(*index).iter());
        all_path_indices.extend(get_path_indices(*index).iter());
    }

    let mut all_branch_indices =
        all_helper_indices.difference(&all_path_indices).cloned().collect::<Vec<_>>();
    all_branch_indices.sort_by(|a: &GeneralizedIndex, b: &GeneralizedIndex| b.cmp(a));
    all_branch_indices
}

pub fn calculate_merkle_root(
    leaf: Node,
    proof: &[Node],
    index: GeneralizedIndex,
) -> Result<Node, Error> {
    let path_length = get_path_length(index)?;
    if path_length != proof.len() {
        return Err(Error::InvalidProof);
    }
    let mut result = leaf;

    let mut hasher = Sha256::new();
    for (i, next) in proof.iter().enumerate() {
        if get_bit(index, i) {
            hasher.update(next);
            hasher.update(result);
        } else {
            hasher.update(result);
            hasher.update(next);
        }
        result.copy_from_slice(&hasher.finalize_reset());
    }
    Ok(result)
}

pub fn verify_merkle_proof(
    leaf: Node,
    proof: &[Node],
    index: GeneralizedIndex,
    root: Node,
) -> Result<(), Error> {
    if calculate_merkle_root(leaf, proof, index)? == root {
        Ok(())
    } else {
        Err(Error::InvalidProof)
    }
}

pub fn calculate_multi_merkle_root(
    leaves: &[Node],
    proof: &[Node],
    indices: &[GeneralizedIndex],
) -> Result<Node, Error> {
    if leaves.len() != indices.len() {
        return Err(Error::InvalidProof);
    }
    let helper_indices = get_helper_indices(indices);
    if proof.len() != helper_indices.len() {
        return Err(Error::InvalidProof);
    }

    let mut objects = HashMap::new();
    for (index, node) in indices.iter().zip(leaves.iter()) {
        objects.insert(*index, *node);
    }
    for (index, node) in helper_indices.iter().zip(proof.iter()) {
        objects.insert(*index, *node);
    }

    let mut keys = objects.keys().cloned().collect::<Vec<_>>();
    keys.sort_by(|a, b| b.cmp(a));

    let mut hasher = Sha256::new();
    let mut pos = 0;
    while pos < keys.len() {
        let key = keys.get(pos).unwrap();
        let key_present = objects.contains_key(key);
        let sibling_present = objects.contains_key(&sibling(*key));
        let parent_index = parent(*key);
        let parent_missing = !objects.contains_key(&parent_index);
        let should_compute = key_present && sibling_present && parent_missing;
        if should_compute {
            let right_index = key | 1;
            let left_index = sibling(right_index);
            let left_input = objects.get(&left_index).expect("contains index");
            let right_input = objects.get(&right_index).expect("contains index");
            hasher.update(left_input);
            hasher.update(right_input);

            let parent = objects.entry(parent_index).or_default();
            parent.copy_from_slice(&hasher.finalize_reset());
            keys.push(parent_index);
        }
        pos += 1;
    }

    let root = *objects.get(&1).expect("contains index");
    Ok(root)
}

pub fn verify_merkle_multiproof(
    leaves: &[Node],
    proof: &[Node],
    indices: &[GeneralizedIndex],
    root: Node,
) -> Result<(), Error> {
    if calculate_multi_merkle_root(leaves, proof, indices)? == root {
        Ok(())
    } else {
        Err(Error::InvalidProof)
    }
}

#[cfg(test)]
mod tests {
    use crate::{HashTreeRoot, List, Node, Path, PathElement, Prove, SimpleSerialize};
    const MAX_TRANSACTIONS_PER_PAYLOAD: usize = 1_048_576;
    const MAX_BYTES_PER_TRANSACTIONS: usize = 1_073_741_824;
    type Transaction = List<u8, MAX_BYTES_PER_TRANSACTIONS>;

    fn compute_and_verify_proof<T: SimpleSerialize>(data: &T, path: Path) {
        let (proof, witness) = data.prove(path).unwrap();
        assert_eq!(witness, data.hash_tree_root().unwrap());
        dbg!(&proof);
        let result = proof.verify(witness);
        if let Err(err) = result {
            panic!("{err} for {proof:?} with witness {witness}")
        }
    }

    #[test]
    fn merkle_multi_proof_asdf() {
        let raw = vec!["02f873011a8405f5e10085037fcc60e182520894f7eaaf75cb6ec4d0e2b53964ce6733f54f7d3ffc880b6139a7cbd2000080c080a095a7a3cbb7383fc3e7d217054f861b890a935adc1adf4f05e3a2f23688cf2416a00875cdc45f4395257e44d709d04990349b105c22c11034a60d7af749ffea2765", "f8708305dc6885029332e35883019a2894500b0107e172e420561565c8177c28ac0f62017f8810ffb80e6cc327008025a0e9c0b380c68f040ae7affefd11979f5ed18ae82c00e46aa3238857c372a358eca06b26e179dd2f7a7f1601755249f4cff56690c4033553658f0d73e26c36fe7815", "f86c0785028fa6ae0082520894098d880c4753d0332ca737aa592332ed2522cd22880d2f09f6558750008026a0963e58027576b3a8930d7d9b4a49253b6e1a2060e259b2102e34a451d375ce87a063f802538d3efed17962c96fcea431388483bbe3860ea9bb3ef01d4781450fbf", "02f87601836384348477359400850517683ba883019a28943678fce4028b6745eb04fa010d9c8e4b36d6288c872b0f1366ad800080c080a0b6b7aba1954160d081b2c8612e039518b9c46cd7df838b405a03f927ad196158a071d2fb6813e5b5184def6bd90fb5f29e0c52671dea433a7decb289560a58416e"];

        let mut transactions_ssz: List<Transaction, MAX_TRANSACTIONS_PER_PAYLOAD> = List::default();

        raw.iter().for_each(|r| {
            let decoded = hex::decode(r).unwrap();
            transactions_ssz.data.push(Transaction::try_from(decoded.as_ref()).unwrap());
        });

        // using gen index formula: 2 * 2^21
        let base_generalized_index = usize::pow(2, 21);
        let generalized_indexes: Vec<PathElement> = vec![
            // prove inclusion of some transactions
            PathElement::Index(base_generalized_index),
            PathElement::Index(base_generalized_index + 2),
        ];

        compute_and_verify_proof(&transactions_ssz, &generalized_indexes);
    }
}

// use crate::aggregation_circuit::AggregationCircuit;
// use crate::aggregation_circuit::PoseidonTranscript;
// use crate::aggregation_circuit::Snark;
use crate::circuit_witness::CircuitWitness;
use crate::circuits::*;
use crate::utils::collect_instance;
use crate::utils::fixed_rng;
// use crate::utils::gen_num_instance;
use crate::utils::gen_proof;
use tracing::{debug, info};
use crate::G1Affine;
use crate::ProverKey;
use crate::ProverParams;
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::{keygen_pk, keygen_vk};
use halo2_proofs::poly::commitment::Params;
use hyper::Uri;
use rand::{thread_rng, Rng};
// use snark_verifier::loader::native::NativeLoader;
// use snark_verifier::system::halo2::compile;
use snark_verifier::system::halo2::transcript::evm::EvmTranscript;
// use snark_verifier::system::halo2::Config as PlonkConfig;
use std::collections::HashMap;
use std::fmt::Write;
use std::fs::File;
use std::net::ToSocketAddrs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;
use tokio::sync::Mutex;
use zkevm_circuits::util::SubCircuit;
use a3_zkevm_common::json_rpc::jsonrpc_request_client;
use a3_zkevm_common::prover::*;
use lazy_static::lazy_static;

const GEN_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(15 * 60);

fn get_param_path(path: &String, k: usize) -> PathBuf {
    // try to automatically choose a file if the path is a folder.
    if Path::new(path).is_dir() {
        Path::new(path).join(format!("{}.bin", k))
    } else {
        Path::new(path).to_path_buf()
    }
}

const RETRY: usize = 3;


lazy_static! {
    pub static ref PK_CACHE: Arc<Mutex<HashMap<String, Arc<ProverKey>>>> = {
        Arc::new(Mutex::new(HashMap::default()))
    };
}

const CIRCUIT_CONFIG_19: CircuitConfig = CircuitConfig {
    block_gas_limit: 6000000,
    max_txs: 10,
    max_calldata: 131072,
    max_bytecode: 131072,
    max_rws: 3161966,
    min_k: 19,
    pad_to: 2097152,
    min_k_aggregation: 26,
    keccak_padding: 336000,
};

//read the kzg param file
fn get_or_gen_param_core(k:usize) -> (Arc<ProverParams>, String) {
    let path = format!("./{}.bin", k);
    let file = File::open(&path).expect("open exist param successfully");
    let params = Arc::new(
        ProverParams::read(&mut std::io::BufReader::new(file))
            .expect("Failed to read params"),
    );
    (params, path.as_str().to_string())   
}

//generate the pk
async fn gen_pk<C: Circuit<Fr>>(
    param: &Arc<ProverParams>,
    circuit: &C,
) -> Result<Arc<ProverKey>,String> {
    let vk = keygen_vk(param.as_ref(), circuit).unwrap();
    let pk = keygen_pk(param.as_ref(), vk, circuit).unwrap();
    let pk = Arc::new(pk);
    Ok(pk)
}


pub async fn generate_witness(block: u64,l2_endpoint:String) -> Result<CircuitWitness, Box<dyn std::error::Error>>{
    let mut retry : usize = 0;
    loop {
        if retry==RETRY {
            return Err(format!(
                "generate_witness failed for block ={}",
                block
            )
            .into());
        }
        let witness = match CircuitWitness::from_rpc(
            &block,
            &l2_endpoint,
        ).await{
            Ok(r) => r,
            Err(_) => {
                info!("get witness data error");
                retry=retry+1;
                continue;
            },
        }; 
        return Ok(witness)
    }
}

pub async fn generate_proof(l2_endpoint:String, block: u64, prover_address: String, l1_signal_service:String ,l2_signal_service:String ,taiko_12:String ,
    meta_hash: String, blockhash: String, parenthash:String ,signalroot:String ,graffiti:String ,gasused:u64 ,parentgasused:u64,blockmaxgasimit:u64,maxtransactionsperblock:u64,maxbytespertxlist:u64) -> Result<ProofResult,String>{

    let mut task_options=ProofRequestOptions::default();
    task_options.block=block;
    task_options.circuit="pi".to_string();
    task_options.l2_rpc=l2_endpoint.clone();
    task_options.l1_signal_service=l1_signal_service;
    task_options.l2_signal_service=l2_signal_service;
    task_options.l2_contract=taiko_12;
    task_options.meta_hash=meta_hash;
    task_options.block_hash=blockhash;
    task_options.parent_hash=parenthash;
    task_options.signal_root=signalroot;
    task_options.graffiti=graffiti;
    task_options.prover=prover_address;
    task_options.gas_used=gasused as u32;
    task_options.parent_gas_used=parentgasused as u32;
    task_options.block_max_gas_limit=blockmaxgasimit;
    task_options.max_transactions_per_block=maxtransactionsperblock;
    task_options.max_bytes_per_tx_list=maxbytespertxlist;

    info!("block task prara is {:?}",task_options);

    info!("zkpool:start to generate the witness of block:{}",block);
    let witness = match generate_witness(
        block,
        l2_endpoint,
    ).await{
        Ok(r) => r,
        Err(e) => {
            info!("get witness data error");
            return Err(e.to_string())
        },
    };
    info!("zkpool:end to generate the witness of block:{}",block);

    let mut circuit_proof = ProofResult::default();

    if witness.l1_txs.len()<=80 {
        let circuit = gen_pi_circuit::<
        { CIRCUIT_CONFIG_19.max_txs },
        { CIRCUIT_CONFIG_19.max_calldata },
        { CIRCUIT_CONFIG_19.max_rws },
        _,>(&witness, &task_options, fixed_rng()).unwrap();

        let (param, _) = get_or_gen_param_core(CIRCUIT_CONFIG_19.min_k);
        circuit_proof.k = param.k() as u8;

        //get pk from cache or generate new 
        let pk_temp = PK_CACHE.clone();
        let mut pk_map = pk_temp.lock().await;
        let pk = match pk_map.get("pi-19") {
            Some(r) => {
              r.clone()
            },
            None => {
                let new_pk = gen_pk(&param,&circuit).await.unwrap();
                pk_map.insert("pi-19".to_string(), new_pk.clone());
                new_pk
            },
        };

        let circuit_instance = circuit.0.instance();
        circuit_proof.instance = collect_instance(&circuit_instance);

        info!("zkpool:start to create proof of block:{}",block);
        let handle = tokio::task::spawn_blocking(move || {
            gen_proof::<
                _,
                _,
                EvmTranscript<G1Affine, _, _, _>,
                EvmTranscript<G1Affine, _, _, _>,
                _,
            >(
                &param,
                &pk,
                circuit,
                circuit_instance.clone(),
                fixed_rng(),
                false, 
                true,  
            )
        });

        //add timeout logic
        let proof = match tokio::time::timeout(GEN_TIMEOUT, handle).await{
            Ok(result) => {
                match result {
                    Ok(r) => r,
                    Err(_) => return Err("timeout occured,ignore it".to_string())
                }
            }
            Err(_) => {
                return Err("timeout occured".to_string())
            },
        };
        info!("zkpool:end to create proof of block:{}",block);
        circuit_proof.proof = proof.clone().into();
        debug!("zkpool:end to process the proof generation of block:{}",block);
        return Ok(circuit_proof)
        } else {
            debug!("ignored the block of {} process due to reason of txs number {} is invalid",block,witness.txs().len());
        }

    Ok(ProofResult::default())

}


fn get_or_gen_param(task_options: &ProofRequestOptions, k: usize) -> (Arc<ProverParams>, String) {
    match &task_options.param {
        Some(v) => {
            let path = get_param_path(v, k);
            let file = File::open(&path).expect("open exist param successfully");
            let params = Arc::new(
                ProverParams::read(&mut std::io::BufReader::new(file))
                    .expect("Failed to read params"),
            );

            (params, path.to_str().unwrap().into())
        }
        None => {
            let param = Arc::new(ProverParams::setup(k as u32, fixed_rng()));
            (param, format!("{}", k))
        }
    }
}

macro_rules! gen_proof {
    ($shared_state:expr, $task_options:expr, $witness:expr, $CIRCUIT:ident) => {{
        let witness = $witness;
        // uncomment for testing purposes
        //let witness = CircuitWitness::dummy(CIRCUIT_CONFIG.block_gas_limit).unwrap();
        let task_options = $task_options;
        let shared_state = $shared_state;

        log::info!("Using circuit parameters: {:#?}", CIRCUIT_CONFIG);

        let mut circuit_proof = ProofResult::default();
        circuit_proof.label = format!(
            "{}-{}",
            task_options.circuit, CIRCUIT_CONFIG.block_gas_limit
        );
        let mut aggregation_proof = ProofResult::default();
        aggregation_proof.label = format!(
            "{}-{}-a",
            task_options.circuit, CIRCUIT_CONFIG.block_gas_limit
        );

        if task_options.mock {
            // only run the mock prover
            let time_started = Instant::now();
            let circuit = $CIRCUIT::<
                { CIRCUIT_CONFIG.max_txs },
                { CIRCUIT_CONFIG.max_calldata },
                { CIRCUIT_CONFIG.max_rws },
                _,
            >(&witness, &task_options, fixed_rng())?;
            circuit_proof.k = CIRCUIT_CONFIG.min_k as u8;
            circuit_proof.instance = collect_instance(&circuit.0.instance());
            let prover =
                MockProver::run(CIRCUIT_CONFIG.min_k as u32, &circuit, circuit.0.instance())
                    .expect("MockProver::run");
            prover.verify_par().expect("MockProver::verify_par");
            circuit_proof.duration = Instant::now().duration_since(time_started).as_millis() as u32;
        } else {
            let (param, param_path) = get_or_gen_param(&task_options, CIRCUIT_CONFIG.min_k);
            circuit_proof.k = param.k() as u8;
            let circuit = $CIRCUIT::<
                { CIRCUIT_CONFIG.max_txs },
                { CIRCUIT_CONFIG.max_calldata },
                { CIRCUIT_CONFIG.max_rws },
                _,
            >(&witness, &task_options, fixed_rng())?;
            // generate and cache the prover key
            let pk = {
                let cache_key = format!(
                    "{}{}{:?}",
                    &task_options.circuit, &param_path, &CIRCUIT_CONFIG
                );
                shared_state
                    .gen_pk(&cache_key, &param, &circuit)
                    .await
                    .map_err(|e| {
                        log::error!("failed to generate pk: {}", e);
                        e.to_string()
                    })?
            };

            let circuit_instance = circuit.0.instance();
            circuit_proof.instance = collect_instance(&circuit_instance);

            if task_options.aggregate {
                // let time_started = Instant::now();
                // let proof = gen_proof::<
                //     _,
                //     _,
                //     PoseidonTranscript<NativeLoader, _>,
                //     PoseidonTranscript<NativeLoader, _>,
                //     _,
                // >(
                //     &param,
                //     &pk,
                //     circuit,
                //     circuit_instance.clone(),
                //     fixed_rng(),
                //     task_options.mock_feedback,
                //     task_options.verify_proof,
                // );
                // circuit_proof.duration =
                //     Instant::now().duration_since(time_started).as_millis() as u32;
                // circuit_proof.proof = proof.clone().into();

                // // aggregate the circuit proof
                // let time_started = Instant::now();
                // let protocol = compile(
                //     param.as_ref(),
                //     pk.get_vk(),
                //     PlonkConfig::kzg().with_num_instance(gen_num_instance(&circuit_instance)),
                // );
                // let snark = Snark::new(protocol, circuit_instance, proof);

                // let (agg_params, agg_param_path) =
                //     get_or_gen_param(&task_options, CIRCUIT_CONFIG.min_k_aggregation);
                // aggregation_proof.k = agg_params.k() as u8;
                // let agg_circuit =
                //     AggregationCircuit::new(agg_params.as_ref(), [snark], fixed_rng());
                // let agg_pk = {
                //     let cache_key = format!(
                //         "{}{}{:?}ag",
                //         &task_options.circuit, &agg_param_path, &CIRCUIT_CONFIG
                //     );
                //     shared_state
                //         .gen_pk(&cache_key, &agg_params, &agg_circuit)
                //         .await
                //         .map_err(|e| e.to_string())?
                // };
                // let agg_instance = agg_circuit.instance();
                // aggregation_proof.instance = collect_instance(&agg_instance);
                // let proof = gen_proof::<
                //     _,
                //     _,
                //     EvmTranscript<G1Affine, _, _, _>,
                //     EvmTranscript<G1Affine, _, _, _>,
                //     _,
                // >(
                //     agg_params.as_ref(),
                //     &agg_pk,
                //     agg_circuit,
                //     agg_instance,
                //     fixed_rng(),
                //     task_options.mock_feedback,
                //     task_options.verify_proof,
                // );
                // aggregation_proof.duration =
                //     Instant::now().duration_since(time_started).as_millis() as u32;
                // aggregation_proof.proof = proof.into();
            } else {
                let time_started = Instant::now();
                let handle = tokio::task::spawn_blocking(move || {
                    gen_proof::<
                        _,
                        _,
                        EvmTranscript<G1Affine, _, _, _>,
                        EvmTranscript<G1Affine, _, _, _>,
                        _,
                    >(
                        &param,
                        &pk,
                        circuit,
                        circuit_instance.clone(),
                        fixed_rng(),
                        task_options.mock_feedback,
                        task_options.verify_proof,
                    )
                });

                let proof = tokio::time::timeout(GEN_TIMEOUT, handle)
                    .await
                    .map_err(|e| {
                        log::error!("gen proof timeout: {}", e);
                        e.to_string()
                    })?
                    .map_err(|e| {
                        log::error!("spawn gen proof task failed: {}", e);
                        e.to_string()
                    })?;

                circuit_proof.duration =
                    Instant::now().duration_since(time_started).as_millis() as u32;
                circuit_proof.proof = proof.clone().into();
            }
        }

        // return
        (CIRCUIT_CONFIG, circuit_proof, aggregation_proof)
    }};
}

#[derive(Clone)]
pub struct RoState {
    // a unique identifier
    pub node_id: String,
    // a `HOSTNAME:PORT` conformant string that will be used for DNS service discovery of other
    // nodes
    pub node_lookup: Option<String>,
}

pub struct RwState {
    pub tasks: Vec<ProofRequest>,
    /// The maximum tasks can be held.
    pub max_tasks: usize,
    pub pk_cache: HashMap<String, Arc<ProverKey>>,
    /// The current active task this instance wants to obtain or is working on.
    pub pending: Option<ProofRequestOptions>,
    /// `true` if this instance started working on `pending`
    pub obtained: bool,
}

#[derive(Clone)]
pub struct SharedState {
    pub ro: RoState,
    pub rw: Arc<Mutex<RwState>>,
}

impl SharedState {
    pub fn new(node_id: String, node_lookup: Option<String>, max_tasks: usize) -> SharedState {
        Self {
            ro: RoState {
                node_id,
                node_lookup,
            },
            rw: Arc::new(Mutex::new(RwState {
                tasks: Vec::new(),
                max_tasks,
                pk_cache: HashMap::new(),
                pending: None,
                obtained: false,
            })),
        }
    }

    /// Will return the result or error of the task if it's completed.
    /// Otherwise enqueues the task and returns `None`.
    /// `retry_if_error` enqueues the task again if it returned with an error
    /// before.
    pub async fn get_or_enqueue(
        &self,
        options: &ProofRequestOptions,
    ) -> Option<Result<Proofs, String>> {
        let mut rw = self.rw.lock().await;

        // task already pending or completed?
        let task = rw.tasks.iter_mut().find(|e| e.options == *options);

        if task.is_some() {
            let mut task = task.unwrap();

            if task.result.is_some() {
                if options.retry && task.result.as_ref().unwrap().is_err() {
                    log::debug!("retrying: {:#?}", task);
                    // will be a candidate in `duty_cycle` again
                    task.result = None;
                    task.edition += 1;
                } else {
                    log::debug!("completed: {:#?}", task);
                    return task.result.clone();
                }
            } else {
                log::debug!("pending: {:#?}", task);
                return None;
            }
        } else {
            // enqueue the task
            let task = ProofRequest {
                options: options.clone(),
                result: None,
                edition: 0,
            };
            log::debug!("enqueue: {:#?}", task);
            rw.tasks.push(task);
        }

        drop(rw);
        self.prune_tasks().await;
        None
    }

    async fn prune_tasks(&self) {
        let mut rw = self.rw.lock().await;
        let max_tasks = rw.max_tasks;
        // limit tasks size if max_tasks != 0
        // TODO: drain completed only.
        if rw.tasks.len() >= max_tasks && max_tasks != 0 {
            rw.tasks
                .sort_by(|a, b| a.options.block.cmp(&b.options.block));
            rw.tasks.drain(0..(max_tasks / 2));
            log::info!(
                "prune tasks to block in [{:?}, {:?}]",
                rw.tasks.first().map(|t| t.options.block),
                rw.tasks.last().map(|t| t.options.block)
            );
        }
    }

    /// Checks if there is anything to do like:
    /// - records if a task completed
    /// - starting a new task
    /// Blocks until completion but releases the lock of `self.rw` in between.
    pub async fn duty_cycle(&self) {
        // fix the 'world' view
        if let Err(err) = self.merge_tasks_from_peers().await {
            log::error!("merge_tasks_from_peers failed with: {}", err);
            return;
        }

        let rw = self.rw.lock().await;
        if rw.pending.is_some() || rw.obtained {
            // already computing
            return;
        }
        // find a pending task
        let tasks: Vec<ProofRequestOptions> = rw
            .tasks
            .iter()
            .filter(|&e| e.result.is_none())
            .map(|e| e.options.clone())
            .collect();
        drop(rw);

        for task in tasks {
            // signals that this node wants to process this task
            log::debug!("trying to obtain {:#?}", task);
            self.rw.lock().await.pending = Some(task);

            // notify other peers
            // wrap the object because it's important to clear `pending` on error
            {
                let self_copy = self.clone();
                let obtain_task =
                    tokio::spawn(
                        async move { self_copy.obtain_task().await.expect("obtain_task") },
                    )
                    .await;

                if obtain_task.is_err() || !obtain_task.unwrap() {
                    self.rw.lock().await.pending = None;
                    log::debug!("failed to obtain task");
                    continue;
                }

                // won the race
                self.rw.lock().await.obtained = true;
                break;
            }
        }

        // needs to be cloned because of long running tasks and
        // the possibility that the task gets removed in the meantime
        let task_options = self.rw.lock().await.pending.clone();
        if task_options.is_none() {
            // nothing to do
            return;
        }

        // succesfully obtained the task
        let task_options = task_options.unwrap();
        log::info!("compute_proof: {:#?}", task_options);

        // Note: this catches any panics for the task itself but will not help in the
        // situation when the process get itself OOM killed, stack overflows etc.
        // This could be avoided by spawning a subprocess for the proof computation
        // instead.

        // spawn a task to catch panics
        let task_result: Result<Result<Proofs, String>, tokio::task::JoinError> = {
            let task_options_copy = task_options.clone();
            let self_copy = self.clone();

            tokio::spawn(async move {
                let witness =
                    CircuitWitness::from_rpc(&task_options_copy.block, &task_options_copy.l2_rpc)
                        .await
                        .map_err(|e| e.to_string())?;

                let (config, circuit_proof, aggregation_proof) = crate::match_circuit_params_txs!(
                    witness.l1_txs.len(),
                    {
                        match task_options_copy.circuit.as_str() {
                            "pi" => {
                                gen_proof!(self_copy, task_options_copy, &witness, gen_pi_circuit)
                            }
                            // "super" => {
                            //     gen_proof!(
                            //         self_copy,
                            //         task_options_copy,
                            //         &witness,
                            //         gen_super_circuit
                            //     )
                            // }
                            // "evm" => {
                            //     gen_proof!(self_copy, task_options_copy, &witness, gen_evm_circuit)
                            // }
                            // "state" => gen_proof!(
                            //     self_copy,
                            //     task_options_copy,
                            //     &witness,
                            //     gen_state_circuit
                            // ),
                            // "tx" => {
                            //     gen_proof!(self_copy, task_options_copy, &witness, gen_tx_circuit)
                            // }
                            // "bytecode" => gen_proof!(
                            //     self_copy,
                            //     task_options_copy,
                            //     &witness,
                            //     gen_bytecode_circuit
                            // ),
                            // "copy" => {
                            //     gen_proof!(self_copy, task_options_copy, &witness, gen_copy_circuit)
                            // }
                            // "exp" => {
                            //     gen_proof!(self_copy, task_options_copy, &witness, gen_exp_circuit)
                            // }
                            // "keccak" => gen_proof!(
                            //     self_copy,
                            //     task_options_copy,
                            //     &witness,
                            //     gen_keccak_circuit
                            // ),
                            _ => panic!("unknown circuit"),
                        }
                    },
                    {
                        return Err(format!(
                            "No circuit parameters found for block with gas used={}",
                            witness.gas_used()
                        ));
                    }
                );

                let res = Proofs {
                    config,
                    circuit: circuit_proof,
                    aggregation: aggregation_proof,
                    gas: witness.gas_used(),
                };

                Ok(res)
            })
            .await
        };

        // convert the JoinError to string - if applicable
        let task_result: Result<Proofs, String> = match task_result {
            Err(err) => match err.is_panic() {
                true => {
                    let panic = err.into_panic();

                    if let Some(msg) = panic.downcast_ref::<&str>() {
                        Err(msg.to_string())
                    } else if let Some(msg) = panic.downcast_ref::<String>() {
                        Err(msg.to_string())
                    } else {
                        Err("unknown panic".to_string())
                    }
                }
                false => Err(err.to_string()),
            },
            Ok(val) => val,
        };

        {
            // done, update the queue
            log::info!("task_result: {:#?}", task_result);

            let mut rw = self.rw.lock().await;
            // clear fields
            rw.pending = None;
            rw.obtained = false;
            // insert task result
            let task = rw.tasks.iter_mut().find(|e| e.options == task_options);
            if let Some(task) = task {
                // found our task, update result
                task.result = Some(task_result);
                task.edition += 1;
            } else {
                // task was already removed in the meantime,
                // assume it's obsolete and forget about it
                log::info!(
                    "task was already removed, ignoring result {:#?}",
                    task_options
                );
            }
        }
    }

    /// Returns `node_id` and `tasks` for this instance.
    /// Normally used for the rpc api.
    pub async fn get_node_information(&self) -> NodeInformation {
        NodeInformation {
            id: self.ro.node_id.clone(),
            tasks: self.rw.lock().await.tasks.clone(),
        }
    }

    /// Pulls `NodeInformation` from all other peers and
    /// merges missing or updated tasks from these peers to
    /// preserve information in case individual nodes are going to be
    /// terminated.
    ///
    /// Always returns `true` otherwise returns with error.
    pub async fn merge_tasks_from_peers(&self) -> Result<bool, String> {
        const LOG_TAG: &str = "merge_tasks_from_peers:";

        if self.ro.node_lookup.is_none() {
            return Ok(true);
        }

        let hyper_client = hyper::Client::new();
        let addrs_iter = self
            .ro
            .node_lookup
            .as_ref()
            .unwrap()
            .to_socket_addrs()
            .map_err(|e| e.to_string())?;

        for addr in addrs_iter {
            let uri = Uri::try_from(format!("http://{}", addr)).map_err(|e| e.to_string())?;
            let peer: NodeInformation =
                jsonrpc_request_client(5000, &hyper_client, &uri, "info", serde_json::json!([]))
                    .await?;

            if peer.id == self.ro.node_id {
                log::debug!("{} skipping self({})", LOG_TAG, peer.id);
                continue;
            }

            log::debug!("{} merging with peer({})", LOG_TAG, peer.id);
            self.merge_tasks(&peer).await;
        }

        Ok(true)
    }

    // TODO: can this be pre-generated to a file?
    // related
    // https://github.com/zcash/halo2/issues/443
    // https://github.com/zcash/halo2/issues/449
    /// Compute or retrieve a proving key from cache.
    async fn gen_pk<C: Circuit<Fr> + Send + Clone + 'static>(
        &self,
        cache_key: &str,
        param: &Arc<ProverParams>,
        circuit: &C,
    ) -> Result<Arc<ProverKey>, Box<dyn std::error::Error>> {
        let mut rw = self.rw.lock().await;
        if !rw.pk_cache.contains_key(cache_key) {
            // drop, potentially long running
            drop(rw);
            let param = param.clone();
            let circuit = circuit.clone();
            let handle = tokio::task::spawn_blocking(move || {
                let vk = keygen_vk(param.as_ref(), &circuit)?;
                let pk = keygen_pk(param.as_ref(), vk, &circuit)?;
                Result::<_, halo2_proofs::plonk::Error>::Ok(Arc::new(pk))
            });
            let pk = tokio::time::timeout(GEN_TIMEOUT, handle).await???;
            // acquire lock and update
            rw = self.rw.lock().await;
            rw.pk_cache.insert(cache_key.to_string(), pk);

            log::info!("ProvingKey: generated and cached key={}", cache_key);
        }

        Ok(rw.pk_cache.get(cache_key).unwrap().clone())
    }

    async fn merge_tasks(&self, node_info: &NodeInformation) {
        const LOG_TAG: &str = "merge_tasks:";
        let mut rw = self.rw.lock().await;

        for peer_task in &node_info.tasks {
            let maybe_task = rw.tasks.iter_mut().find(|e| e.options == peer_task.options);

            if let Some(existent_task) = maybe_task {
                if existent_task.edition >= peer_task.edition {
                    // fast case
                    log::debug!("{} up to date {:#?}", LOG_TAG, existent_task);
                    continue;
                }

                // update result, edition
                existent_task.edition = peer_task.edition;
                existent_task.result = peer_task.result.clone();
                log::debug!("{} updated {:#?}", LOG_TAG, existent_task);
            } else {
                // copy task
                rw.tasks.push(peer_task.clone());
                log::debug!("{} new task {:#?}", LOG_TAG, peer_task);
            }
        }
        drop(rw);
        self.prune_tasks().await;
    }

    /// Tries to obtain `self.rw.pending` by querying all other peers
    /// about their current task item that resolves to either
    /// winning or losing the task depending on the algorithm.
    ///
    /// Expects `self.rw.pending` to be not `None`
    async fn obtain_task(&self) -> Result<bool, String> {
        const LOG_TAG: &str = "obtain_task:";

        let task_options = self
            .rw
            .lock()
            .await
            .pending
            .as_ref()
            .expect("pending task")
            .clone();

        if self.ro.node_lookup.is_none() {
            return Ok(true);
        }

        // resolve all other nodes for this service
        let hyper_client = hyper::Client::new();
        let addrs_iter = self
            .ro
            .node_lookup
            .as_ref()
            .unwrap()
            .to_socket_addrs()
            .map_err(|e| e.to_string())?;
        for addr in addrs_iter {
            let uri = Uri::try_from(format!("http://{}", addr)).map_err(|e| e.to_string())?;
            let peer: NodeStatus =
                jsonrpc_request_client(5000, &hyper_client, &uri, "status", serde_json::json!([]))
                    .await?;

            if peer.id == self.ro.node_id {
                log::debug!("{} skipping self({})", LOG_TAG, peer.id);
                continue;
            }

            if let Some(peer_task) = peer.task {
                if peer_task == task_options {
                    // a slight chance to 'win' the task
                    if !peer.obtained && peer.id > self.ro.node_id {
                        log::debug!("{} won task against {}", LOG_TAG, peer.id);
                        // continue the race against the remaining peers
                        continue;
                    }

                    log::debug!("{} lost task against {}", LOG_TAG, peer.id);
                    // early return
                    return Ok(false);
                }
            }
        }

        // default
        Ok(true)
    }

    pub fn random_worker_id() -> String {
        // derive a (sufficiently large) random worker id
        const N: usize = 16;
        let mut arr = [0u8; N];
        thread_rng().fill(&mut arr[..]);
        let mut node_id = String::with_capacity(N * 2);
        for byte in arr {
            write!(node_id, "{:02x}", byte).unwrap();
        }

        node_id
    }
}

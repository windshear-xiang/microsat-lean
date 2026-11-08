#!/bin/bash
# One shard of tools/cluster_bench.py. Submit from the repository root:
#   sbatch --job-name=msat-0 tools/cluster/bench.sbatch RUN SHARD SHARDS
# CPU-only on preempt: the QoS is mandatory, at most 32 CPUs per job and 64 per user.
# The job is resumable, so a requeue (preemption) or a resubmission just continues.
#SBATCH --partition=preempt
#SBATCH --qos=preempt_cpu_qos
#SBATCH --cpus-per-task=8
#SBATCH --mem=32G
#SBATCH --time=3-00:00:00
#SBATCH --requeue
#SBATCH --output=/home/%u/logs/sbatch/%j-%x-%N.out
set -euo pipefail
cd "$SLURM_SUBMIT_DIR"
echo "job $SLURM_JOB_ID on $(hostname), restart count ${SLURM_RESTART_COUNT:-0}"
# Parallel solver processes in this job: one per CPU unless WORKERS is set
# (e.g. sbatch --export=ALL,WORKERS=4 ... to leave cores idle and reduce interference).
exec python3 -B tools/cluster_bench.py shard "$1" "$2" "$3" --workers "${WORKERS:-$SLURM_CPUS_PER_TASK}"

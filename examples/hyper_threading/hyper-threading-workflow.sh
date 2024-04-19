#!/bin/bash

# Define a list of RAYON_NUM_THREADS
thread_counts=(1 2 4 6 8 16 )

# Define binary names
binaries=("hyper_threading_main" "hyper_threading_pr")

echo -e "**Hyper Thereading Benchmark results**" >> result.md
printf "\n\n" >> result.md

# Iter over thread_counts
for threads in "${thread_counts[@]}"; do
    # Initialize hyperfine command
    cmd="hyperfine -r 2"
    
    # Add each binary to the command with the current threads value
    for binary in "${binaries[@]}"; do
        cmd+=" -n \"${binary} threads: ${threads}\" 'RAYON_NUM_THREADS=${threads} ./${binary}'"
    done
    
    # Execute 
    echo "Running benchmark for ${threads} threads"
    printf "\n\n" >> result.md
    echo -e $cmd >> result.md 
    eval $cmd >> result.md
    printf "\n\n" >> result.md
done

{
  echo -e '```'
  cat result.md
  echo -e '```'
} > temp_result.md && mv temp_result.md result.md

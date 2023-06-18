#!/bin/bash
parent_path=$( cd "$(dirname "${BASH_SOURCE[0]}")" ; pwd -P )

cp $parent_path/../build/bin/duper $parent_path/bin/duper
cd $parent_path
tar -cf duper_starexec.tar bin
while true
do 
    go test -v -run TestRaft_FiveServersOneFailing$ | tee output.log
    if [ $? -neq 0 ]; then 
        break
    fi 
done

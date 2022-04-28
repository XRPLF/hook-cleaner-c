stat ../cleaner > /dev/null 2> /dev/null
if [ ! "$?" -eq "0" ];
then
    pushd
    cd ..
    make
    popd
    stat ../cleaner > /dev/null 2> /dev/null
    if [ ! "$?" -eq "0" ];
    then
        echo "Hook cleaner not found in parent directory, build attempt failed."
        exit 1
    fi
fi

which wasm2wat > /dev/null 2> /dev/null
if [ ! "$?" -eq "0" ];
then
    echo "wasm2wat not found, please install wabt"
    exit 2
fi

PASSED=0
COUNT=0
for i in `ls *.wasm`; do
    COUNT=`expr $COUNT + 1`
    rm /tmp/t.wasm
    ../cleaner $i /tmp/t.wasm > /dev/null 2> /dev/null
    R1="$?"
    wasm2wat /tmp/t.wasm > /dev/null 2> /dev/null
    R2="$?"

    if [ $R1 -eq "0" ];
    then
        if [ $R2 -eq "0" ];
        then
            echo TEST $COUNT -- $i -- PASS
            PASSED=`expr $PASSED + 1`
        else
            echo TEST $COUNT -- $i -- FAIL wasm2wat
        fi
    else
        echo TEST $COUNT -- $i -- FAIL
    fi
done

if [ "$PASSED" -eq "$COUNT" ];
then
    echo All tests passed!
else
    echo "NOT All tests passed: `expr $COUNT - $PASSED` failed."
fi


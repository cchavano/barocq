check()
{
    H1=`sha256hmac $1 | cut -d' ' -f1`
    if [ -e $2 ]; then
	H2=`sha256hmac $2 | cut -d' ' -f1`
	[[ $H1 != $H2 ]]
	return 
    else
	return 0
    fi
}

for file1 in $1/*; do
    file2=$2/$(basename $file1)
    $(check $file1 $file2)
    if [[ $? = 0 ]]; then
	echo SYNC $file1 $file2
	cp $file1 $file2
    fi
done 

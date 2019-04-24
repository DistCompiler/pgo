timestamp=$(date +"%T")
for i in {1..3}
do
  echo "stopping etcd on server-$i"
  ssh server-$i "sudo systemctl stop etcd"
done

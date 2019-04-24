timestamp=$(date +"%T")
for i in {1..3}
do
  echo "preparing etcd on server-$i"
  ssh server-$i "sudo mv /var/lib/etcd/default data-$timestamp.etcd; sudo chown -R pgo:pgo data-$timestamp.etcd; sudo mkdir /var/lib/etcd/default; sudo chown etcd:etcd /var/lib/etcd/default; sudo chmod 700 /var/lib/etcd/default"
done
for i in {1..3}
do
  echo "starting etcd on server-$i"
  ssh server-$i "sudo systemctl start etcd" &
done

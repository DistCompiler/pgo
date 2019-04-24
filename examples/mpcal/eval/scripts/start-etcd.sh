timestamp=$(date +"%T")
for i in {1..3}
do
  echo "starting etcd on server-$i"
  ssh server-$i "sudo cp -r /var/lib/etcd/default/ data-$timestamp.etcd; sudo chown -R pgo:pgo data-$timestamp.etcd; sudo rm -rf /var/lib/etcd/default/* ; sudo systemctl start etcd"
done

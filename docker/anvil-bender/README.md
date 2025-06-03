# Docker with anvil-zksync and ohbender

To build - run from **main zksync-airbender** directory:

```shell
docker build -f docker/anvil-bender/Dockerfile -t ohbender:latest .
```

To run:

```shell
docker run \
  --gpus all \
  -p 8011:8011 \
  -p 3030:3030 \
  --name ohbender \
  matterlabs/ohbender:latest
```

After that, you can send transactions to localhost:8011, and check the prover status on localhost:3030

```
cast send -r http://localhost:8011 0x5fbdb2315678afecb367f032d93f642f64180aa3 --value 100  --private-key 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80  --gas-limit 100000000
```



## Troubleshooting


### Making GPU visible in docker

You can check if your GPUs are visible in docker, by running:

```shell
docker run --rm --gpus all nvidia/cuda:12.6.0-runtime-ubuntu24.04 nvidia-smi
```

If it fails, you have to install nvidia container toolkit:


https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/install-guide.html


Instructions:

```shell
curl -fsSL https://nvidia.github.io/libnvidia-container/gpgkey | sudo gpg --dearmor -o /usr/share/keyrings/nvidia-container-toolkit-keyring.gpg \
  && curl -s -L https://nvidia.github.io/libnvidia-container/stable/deb/nvidia-container-toolkit.list | \
    sed 's#deb https://#deb [signed-by=/usr/share/keyrings/nvidia-container-toolkit-keyring.gpg] https://#g' | \
    sudo tee /etc/apt/sources.list.d/nvidia-container-toolkit.list

sudo apt-get update
sudo apt-get install -y nvidia-container-toolkit
sudo nvidia-ctk runtime configure --runtime=docker
sudo systemctl restart docker
```
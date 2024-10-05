use dev_utils::{get_mem_usage, ByteSize};
use loro::{LoroDoc, LoroMap};
use std::time::Instant;

pub fn main() {
    let node_num = 1_000_000;
    let op_per_node = 100;

    let bytes = {
        let start = Instant::now();
        let doc = LoroDoc::new();
        let files = doc.get_map("files");
        let mut nodes = vec![];
        for i in 0..node_num {
            if i % 1000 == 0 {
                doc.set_peer_id(i).unwrap();
            }

            nodes.push(
                files
                    .insert_container(&i.to_string(), LoroMap::new())
                    .unwrap(),
            );
        }

        println!("Create 1M Nodes Duration {:?}", start.elapsed());
        for i in 0..op_per_node {
            println!(
                "Percentage: {:.2}% {:?}",
                i as f64 / op_per_node as f64 * 100.0,
                get_mem_usage()
            );
            for (k, node) in nodes.iter().enumerate() {
                if k % 1000 == 0 && k != 0 {
                    doc.set_peer_id(k as u64 - 1).unwrap();
                }

                node.insert("key", "value".to_string()).unwrap();
                node.insert("counter", i).unwrap();
            }
            doc.compact_change_store();
        }

        println!("Total Ops.len={}", doc.len_ops());
        println!("100M ops duration {:?}", start.elapsed());
        println!("Mem {:?}", get_mem_usage());

        let start = Instant::now();
        let snapshot = doc.export(loro::ExportMode::Snapshot).unwrap();
        println!("Export snapshot duration {:?}", start.elapsed());
        println!("Mem {:?}", get_mem_usage());

        let start = Instant::now();
        let new_doc = LoroDoc::new();
        new_doc.import(&snapshot).unwrap();
        println!("Import snapshot duration {:?}", start.elapsed());

        let start = Instant::now();
        let _s = new_doc.export(loro::ExportMode::Snapshot);
        println!("New doc export snapshot time {:?}", start.elapsed());
        println!("Mem {:?}", get_mem_usage());
        snapshot
    };

    let trimmed_snapshot = {
        println!("Snapshot size {:?}", ByteSize(bytes.len()));
        let doc = LoroDoc::new();
        doc.import(&bytes).unwrap();
        println!("Mem usage after import snapshot {:?}", get_mem_usage());
        let start = Instant::now();
        let _v = doc.get_deep_value();
        println!("GetValue duration {:?}", start.elapsed());
        println!("Mem usage after getting value {:?}", get_mem_usage());
        let start = Instant::now();
        let _trimmed_bytes = doc.export(loro::ExportMode::Snapshot).unwrap();
        println!("ReExport Snapshot Duration {:?}", start.elapsed());
        let start = Instant::now();
        let trimmed_bytes = doc
            .export(loro::ExportMode::trimmed_snapshot(&doc.oplog_frontiers()))
            .unwrap();
        println!("Export TrimmedSnapshot Duration {:?}", start.elapsed());
        println!("TrimmedSnapshot size {:?}", ByteSize(trimmed_bytes.len()));
        trimmed_bytes
    };

    {
        let start = Instant::now();
        let doc = LoroDoc::new();
        doc.import(&trimmed_snapshot).unwrap();
        println!("Import gc snapshot time: {:?}", start.elapsed());
        println!("Mem usage {:?}", get_mem_usage());
        let start = Instant::now();
        let _v = doc.get_deep_value();
        println!("GetValue duration {:?}", start.elapsed());
        println!("Mem usage after getting value {:?}", get_mem_usage());
    }
}

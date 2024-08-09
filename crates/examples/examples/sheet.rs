use dev_utils::get_mem_usage;
use examples::sheet::init_large_sheet;
use loro::ID;

pub fn main() {
    let doc = init_large_sheet(10_000_000);
    // let doc = init_large_sheet(10_000);
    doc.commit();
    let allocated = get_mem_usage();
    println!("Allocated bytes for 10M cells spreadsheet: {}", allocated);

    doc.checkout(&ID::new(doc.peer_id(), 100).into()).unwrap();

    doc.checkout_to_latest();
    let after_checkout = get_mem_usage();
    println!("Allocated bytes after checkout: {}", after_checkout);
}

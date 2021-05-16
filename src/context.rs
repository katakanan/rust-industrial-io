// libiio-sys/src/context.rs
//
// Copyright (c) 2018, Frank Pagliughi
//
// Licensed under the MIT license:
//   <LICENSE or http://opensource.org/licenses/MIT>
// This file may not be copied, modified, or distributed except according
// to those terms.
//
//! Industrial I/O Contexts.
//!

use std::ffi::CString;
use std::os::raw::{c_int, c_uint};
use std::ptr;
use std::rc::Rc;
use std::time::Duration;

use super::*;
use crate::bindings as ffi;

/// An Industrial I/O Context
///
/// Since the IIO library isn't thread safe, this object cannot be Send or
/// Sync.
///
/// This object maintains a reference counted pointer to the context object
/// of the underlying library's iio_context object. Once all references to
/// the Context object have been dropped, the underlying iio_context will be
/// destroyed. This is done to make creation and use of a single Device more
/// ergonomic by removing the need to manage the lifetime of the Context.
#[derive(Debug, Clone)]
pub struct Context {
    inner: Rc<InnerContext>,
}

/// This holds a pointer to the library context.
/// When it is dropped, the library context is destroyed.
#[derive(Debug)]
struct InnerContext {
    pub(crate) ctx: *mut ffi::iio_context,
}

impl Drop for InnerContext {
    fn drop(&mut self) {
        unsafe { ffi::iio_context_destroy(self.ctx) };
    }
}

impl Context {
    /// Creates a default context from a local or remote IIO device.
    ///
    /// @note This will create a network context if the IIOD_REMOTE
    /// environment variable is set to the hostname where the IIOD server
    /// runs. If set to an empty string, the server will be discovered using
    /// ZeroConf. If the environment variable is not set, a local context
    /// will be created instead.
    pub fn new() -> Result<Context> {
        let ctx = unsafe { ffi::iio_create_default_context() };
        if ctx.is_null() {
            return Err(std::io::Error::last_os_error().into());
        }
        Ok(Context {
            inner: Rc::new(InnerContext { ctx }),
        })
    }

    /// Creates a context from a URI
    ///
    /// This can create a local, network, or XML context as specified by
    /// the URI using the preambles:
    ///   * "local:"  - a local context
    ///   * "xml:"  - an xml (file) context
    ///   * "ip:"  - a network context
    ///   * "usb:"  - a USB backend
    ///   * "serial:"  - a serial backend
    pub fn create_from_uri(uri: &str) -> Result<Context> {
        let uri = CString::new(uri)?;
        let ctx = unsafe { ffi::iio_create_context_from_uri(uri.as_ptr()) };
        if ctx.is_null() {
            return Err(std::io::Error::last_os_error().into());
        }
        Ok(Context {
            inner: Rc::new(InnerContext { ctx }),
        })
    }

    /// Creates a context from a network device
    pub fn create_network(host: &str) -> Result<Context> {
        let host = CString::new(host)?;
        let ctx = unsafe { ffi::iio_create_network_context(host.as_ptr()) };
        if ctx.is_null() {
            return Err(std::io::Error::last_os_error().into());
        }
        Ok(Context {
            inner: Rc::new(InnerContext { ctx }),
        })
    }

    /// Creates a context from an XML file
    pub fn create_xml(xml_file: &str) -> Result<Context> {
        let xml_file = CString::new(xml_file)?;
        let ctx = unsafe { ffi::iio_create_xml_context(xml_file.as_ptr()) };
        if ctx.is_null() {
            return Err(std::io::Error::last_os_error().into());
        }
        Ok(Context {
            inner: Rc::new(InnerContext { ctx }),
        })
    }

    /// Creates a context from XML data in memory
    pub fn create_xml_mem(xml: &str) -> Result<Context> {
        let n = xml.len() as ffi::size_t;
        let xml = CString::new(xml)?;
        let ctx = unsafe { ffi::iio_create_xml_context_mem(xml.as_ptr(), n) };
        if ctx.is_null() {
            return Err(std::io::Error::last_os_error().into());
        }
        Ok(Context {
            inner: Rc::new(InnerContext { ctx }),
        })
    }

    /// Get the name of the context.
    /// This should be "local", "xml", or "network" depending on how the context was created.
    pub fn name(&self) -> String {
        let pstr = unsafe { ffi::iio_context_get_name(self.inner.ctx) };
        cstring_opt(pstr).unwrap_or_default()
    }

    /// Get a description of the context
    pub fn description(&self) -> String {
        let pstr = unsafe { ffi::iio_context_get_description(self.inner.ctx) };
        cstring_opt(pstr).unwrap_or_default()
    }

    /// Obtain the XML representation of the context.
    pub fn xml(&self) -> String {
        let pstr = unsafe { ffi::iio_context_get_xml(self.inner.ctx) };
        cstring_opt(pstr).unwrap_or_default()
    }

    /// Gets the number of context-specific attributes
    pub fn num_attrs(&self) -> usize {
        let n = unsafe { ffi::iio_context_get_attrs_count(self.inner.ctx) };
        n as usize
    }

    /// Gets the name and value of the context-specific attributes.
    /// Note that this is different than the same function for other IIO
    /// types, in that this retrieves both the name and value of the
    /// attributes in a single call.
    pub fn get_attr(&self, idx: usize) -> Result<(String, String)> {
        let mut pname: *const c_char = ptr::null();
        let mut pval: *const c_char = ptr::null();

        let ret = unsafe {
            ffi::iio_context_get_attr(self.inner.ctx, idx as c_uint, &mut pname, &mut pval)
        };
        if ret < 0 {
            // return Err(errno::from_i32(ret).into());
            return Err(std::io::Error::last_os_error().into());
        }
        let name = cstring_opt(pname);
        let val = cstring_opt(pval);
        if name.is_none() || val.is_none() {
            return Err(Error::General("String conversion error".into()));
        }
        Ok((name.unwrap(), val.unwrap()))
    }

    /// Gets an iterator for the attributes in the context
    pub fn attributes(&self) -> AttrIterator {
        AttrIterator { ctx: self, idx: 0 }
    }

    /// Sets the timeout for I/O operations
    ///
    /// `timeout` The timeout. A value of zero specifies that no timeout
    ///     should be used.
    pub fn set_timeout(&mut self, timeout: Duration) -> Result<()> {
        let ms: u64 = 1000 * timeout.as_secs() + u64::from(timeout.subsec_millis());
        self.set_timeout_ms(ms)
    }

    /// Sets the timeout for I/O operations, in milliseconds
    ///
    /// `timeout` The timeout, in ms. A value of zero specifies that no
    ///     timeout should be used.
    pub fn set_timeout_ms(&mut self, ms: u64) -> Result<()> {
        let ret = unsafe { ffi::iio_context_set_timeout(self.inner.ctx, ms as c_uint) };
        sys_result(ret, ())
    }

    /// Get the number of devices in the context
    pub fn num_devices(&self) -> usize {
        unsafe { ffi::iio_context_get_devices_count(self.inner.ctx) as usize }
    }

    /// Gets a device by index
    pub fn get_device(&self, idx: usize) -> Result<Device> {
        let dev = unsafe { ffi::iio_context_get_device(self.inner.ctx, idx as c_uint) };
        if dev.is_null() {
            return Err(Error::InvalidIndex);
        }
        Ok(Device {
            dev,
            ctx: self.clone(),
        })
    }

    /// Try to find a device by name or ID
    /// `name` The name or ID of the device to find
    pub fn find_device(&self, name: &str) -> Option<Device> {
        let name = CString::new(name).unwrap();
        let dev = unsafe { ffi::iio_context_find_device(self.inner.ctx, name.as_ptr()) };
        if dev.is_null() {
            None
        } else {
            Some(Device {
                dev,
                ctx: self.clone(),
            })
        }
    }

    /// Gets an iterator for all the devices in the context.
    pub fn devices(&self) -> DeviceIterator {
        DeviceIterator { ctx: self, idx: 0 }
    }

    /// Destroy the context
    ///
    /// This consumes the context to destroy the instance.
    pub fn destroy(self) {}

    pub fn autodetect_context(rtn: bool, name_str: String, scan_str: String) -> Result<Context> {
        //should it be &str?
        const BUF_SIZE: usize = 16384;
        let scan = if scan_str == "" {
            std::ptr::null_mut()
        } else {
            match CString::new(scan_str) {
                Ok(tmp) => tmp.as_ptr(),
                Err(_) => std::ptr::null_mut(),
            }
        };

        let _name = if name_str == "" {
            std::ptr::null_mut()
        } else {
            match CString::new(name_str) {
                Ok(tmp) => tmp.as_ptr(),
                Err(_) => std::ptr::null_mut(),
            }
        };

        let scan_ctx: *mut ffi::iio_scan_context = unsafe { ffi::iio_create_scan_context(scan, 0) };

        if scan_ctx == std::ptr::null_mut() {
            eprintln!("Unable to create scan context");
            return Err(std::io::Error::last_os_error().into());
        }

        let info: Box<*mut ffi::iio_context_info> =
            Box::new(std::ptr::null_mut() as *mut ffi::iio_context_info);
        let mut pinfo = Box::into_raw(info);

        let ret = unsafe { ffi::iio_scan_context_get_info_list(scan_ctx, &mut pinfo) };

        if ret < 0 {
            let mut err_str = vec![' ' as c_char; BUF_SIZE];
            let pbuf = err_str.as_mut_ptr();
            let err = (-ret) as c_int;
            unsafe { ffi::iio_strerror(err, pbuf, BUF_SIZE as ffi::size_t) };

            let msg = unsafe {
                if err_str.contains(&0) {
                    CStr::from_ptr(pbuf).to_owned()
                } else {
                    let slc =
                        str::from_utf8(slice::from_raw_parts(pbuf as *mut u8, BUF_SIZE)).unwrap();
                    CString::new(slc).unwrap()
                }
            };

            eprintln!("Scannig for IIO contexts failed {}", msg.to_string_lossy());
            unsafe { ffi::iio_scan_context_destroy(scan_ctx) };
            return Err(std::io::Error::last_os_error().into());
        }

        if ret == 0 {
            println!("No IIO context found.");
            unsafe { ffi::iio_context_info_list_free(pinfo) };
            unsafe { ffi::iio_scan_context_destroy(scan_ctx) };
            return Err(Error::General(String::from("No IIO context found.")));
        }

        if rtn && ret == 1 {
            let info = unsafe { slice::from_raw_parts(pinfo, ret as usize).to_vec() };
            let uri = (unsafe { CStr::from_ptr(ffi::iio_context_info_get_uri(info[0])) })
                .to_string_lossy()
                .into_owned();
            println!("Using auto-detected IIO context at URI");
            return Context::create_from_uri(uri.as_str());
        } else {
            if rtn {
                eprintln!("Multiple contexts founds. Please select one using --uri:");
            } else {
                println!("Available contexts:");
            }

            let info = unsafe { slice::from_raw_parts(pinfo, ret as usize).to_vec() };
            for i in 0..ret {
                let description = (unsafe {
                    CStr::from_ptr(ffi::iio_context_info_get_description(info[i as usize]))
                })
                .to_string_lossy();
                let uri =
                    (unsafe { CStr::from_ptr(ffi::iio_context_info_get_uri(info[i as usize])) })
                        .to_string_lossy();
                println!("\t{}: {} [{}]", i, description, uri);
            }
        }
        // println!("{:?}", ret);
        unsafe { ffi::iio_context_info_list_free(pinfo) };
        unsafe { ffi::iio_scan_context_destroy(scan_ctx) }
        Err(Error::General(String::from("Select Context")))
    }
}

impl PartialEq for Context {
    /// Two contexts are the same if they refer to the same underlying
    /// object in the library.
    fn eq(&self, other: &Context) -> bool {
        self.inner.ctx == other.inner.ctx
    }
}

/// Iterator over the Devices in a Context
pub struct DeviceIterator<'a> {
    ctx: &'a Context,
    idx: usize,
}

impl<'a> Iterator for DeviceIterator<'a> {
    type Item = Device;

    fn next(&mut self) -> Option<Self::Item> {
        match self.ctx.get_device(self.idx) {
            Ok(dev) => {
                self.idx += 1;
                Some(dev)
            }
            Err(_) => None,
        }
    }
}

/// Iterator over the attributes in a Context
pub struct AttrIterator<'a> {
    ctx: &'a Context,
    idx: usize,
}

impl<'a> Iterator for AttrIterator<'a> {
    type Item = (String, String);

    fn next(&mut self) -> Option<Self::Item> {
        match self.ctx.get_attr(self.idx) {
            Ok(name_val) => {
                self.idx += 1;
                Some(name_val)
            }
            Err(_) => None,
        }
    }
}

// --------------------------------------------------------------------------
//                              Unit Tests
// --------------------------------------------------------------------------

// Note: These tests assume that the IIO Dummy kernel module is loaded
// locally with a device created. See the `load_dummy.sh` script.

#[cfg(test)]
mod tests {
    use super::*;

    // See that we get the default context.
    #[test]
    fn default_context() {
        let ctx = Context::new();
        assert!(ctx.is_ok());
        //let ctx = ctx.unwrap();
    }

    // Clone a context and make sure it's reported as same one.
    #[test]
    fn clone_context() {
        let ctx = Context::new();
        assert!(ctx.is_ok());
        let ctx = ctx.unwrap();

        let ctx2 = ctx.clone();
        assert!(ctx == ctx2);
    }

    // See that device iterator gets the correct number of devices.
    #[test]
    fn dev_iterator_count() {
        let ctx = Context::new().unwrap();
        let ndev = ctx.num_devices();
        assert!(ndev != 0);
        assert!(ctx.devices().count() == ndev);
    }

    // See that the description gives back something.
    #[test]
    fn name() {
        let ctx = Context::new().unwrap();
        let name = ctx.name();
        println!("Context name: {}", name);
        assert!(name == "local" || name == "network");
    }

    // See that the description gives back something.
    #[test]
    fn description() {
        let ctx = Context::new().unwrap();
        let desc = ctx.description();
        println!("Context description: {}", desc);
        assert!(!desc.is_empty());
    }

    #[test]
    fn detext() {
        let _ = Context::autodetect_context(false, String::from(""), String::from(""));
    }
}

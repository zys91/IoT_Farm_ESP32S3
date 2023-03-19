// Copyright 2019-2021 Espressif Systems (Shanghai) PTE LTD
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "cJSON.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/queue.h"
#include "freertos/event_groups.h"

#include "lwip/sockets.h"
#include "lwip/dns.h"
#include "lwip/netdb.h"
#include <time.h>
#include <sys/time.h>

#include "esp_system.h"
#include "esp_wifi.h"
#include "esp_event.h"
#include "esp_sntp.h"
#include "soc/efuse_reg.h"
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "esp_err.h"
#include "sys/time.h"
#include "driver/uart.h"
#include "driver/gpio.h"
#include "mqtt_client.h"
#include "uvc_stream.h"
#include "esp32s3/spiram.h"
#include "mbedtls/base64.h"
#include "esp_ota_ops.h"
#include "esp_http_client.h"
#include "esp_https_ota.h"
#include "nvs.h"
#include "nvs_flash.h"
#include "esp_smartconfig.h"

#include "lwip/err.h"
#include "lwip/sockets.h"
#include "lwip/sys.h"
#include <lwip/netdb.h>

/* USB PIN fixed in esp32-s2, can not use io matrix */
#define BOARD_USB_DP_PIN 20
#define BOARD_USB_DN_PIN 19

/* USB Camera Descriptors Related MACROS,
the quick demo skip the standred get descriptors process,
users need to get params from camera descriptors from PC side,
eg. run `lsusb -v` in linux,
then hardcode the related MACROS below
*/
#define DESCRIPTOR_CONFIGURATION_INDEX 1
#define DESCRIPTOR_FORMAT_MJPEG_INDEX 1

#define DESCRIPTOR_FRAME_320_240_INDEX 1
#define DESCRIPTOR_FRAME_176_144_INDEX 2
#define DESCRIPTOR_FRAME_160_120_INDEX 3

#define DESCRIPTOR_FRAME_5FPS_INTERVAL 2000000
#define DESCRIPTOR_FRAME_10FPS_INTERVAL 1000000
#define DESCRIPTOR_FRAME_15FPS_INTERVAL 666666
#define DESCRIPTOR_FRAME_20FPS_INTERVAL 500000
#define DESCRIPTOR_FRAME_30FPS_INTERVAL 333333

#define DESCRIPTOR_STREAM_INTERFACE_INDEX 1
#define DESCRIPTOR_STREAM_INTERFACE_ALT_MPS_512 4

#define DESCRIPTOR_STREAM_ISOC_ENDPOINT_ADDR 0x82

#define UVC_FRAME_WIDTH 320
#define UVC_FRAME_HEIGHT 240
#define UVC_XFER_BUFFER_SIZE (32 * 1024) // Double buffer
#define UVC_FRAME_INDEX DESCRIPTOR_FRAME_320_240_INDEX
#define UVC_FRAME_INTERVAL DESCRIPTOR_FRAME_20FPS_INTERVAL

/* max packet size of esp32-s2/s3 is 1*512, bigger is not supported*/
#define UVC_ISOC_EP_MPS 512
#define UVC_ISOC_INTERFACE_ALT DESCRIPTOR_STREAM_INTERFACE_ALT_MPS_512

typedef enum
{
    PIXFORMAT_RGB565,    // 2BPP/RGB565
    PIXFORMAT_YUV422,    // 2BPP/YUV422
    PIXFORMAT_GRAYSCALE, // 1BPP/GRAYSCALE
    PIXFORMAT_JPEG,      // JPEG/COMPRESSED
    PIXFORMAT_RGB888,    // 3BPP/RGB888
    PIXFORMAT_RAW,       // RAW
    PIXFORMAT_RGB444,    // 3BP2P/RGB444
    PIXFORMAT_RGB555,    // 3BP2P/RGB555
} pixformat_t;

/**
 * @brief Data structure of camera frame buffer
 */
typedef struct
{
    uint8_t *buf;             /*!< Pointer to the pixel data */
    size_t len;               /*!< Length of the buffer in bytes */
    size_t width;             /*!< Width of the buffer in pixels */
    size_t height;            /*!< Height of the buffer in pixels */
    pixformat_t format;       /*!< Format of the pixel data */
    struct timeval timestamp; /*!< Timestamp since boot of the first DMA buffer of the frame */
} camera_fb_t;

#define BIT1_NEW_FRAME_START (0x01 << 1)
#define BIT2_NEW_FRAME_END (0x01 << 2)
static const char *TAG = "Farm";
static EventGroupHandle_t s_evt_handle;
static camera_fb_t s_fb = {0};
esp_mqtt_client_handle_t client;
wifi_config_t s_wifi_config;
static int s_retry_num = 0;
static int max_retry_num = 5;

/* FreeRTOS event group to signal when we are connected*/
static EventGroupHandle_t s_wifi_event_group;
static QueueHandle_t uart1_queue;

#define EX_UART_NUM UART_NUM_1
#define UART1TX_PIN GPIO_NUM_17
#define UART1RX_PIN GPIO_NUM_18
#define PATTERN_CHR_NUM (1) /*!< Set the number of consecutive and identical characters received by receiver which defines a UART pattern*/

#define BUF_SIZE (1024)
#define RD_BUF_SIZE (BUF_SIZE)

#define WIFI_CONNECTED_BIT BIT0
#define WIFI_FAIL_BIT BIT1

#define CONNECTED_BIT BIT0
#define ESPTOUCH_DONE_BIT BIT1

static uint8_t MAC[6];
static char CID[7];
static char UID[20] = "";
static char MQTT_CLIENT_ID[20];
static const char *MQTT_BROKER_URL = "ws://127.0.0.1:8083/mqtt";
static const char *Update_SERVER_URL = "http://127.0.0.1:8080/res/esp-release.bin";
static bool userOnlineStatus = false;
static bool WiFiConnection = false;
static int mute = 2;
static int temp;
static int humi;
static float lux;
static int weight;
static float soilTemp;
static float soilHumi;
static int soilEC;
static float soilPH;
static int waterHeight;
static int light_pwm;
static int fan_pwm;
static int waterPump_pwm;
static int8_t operateMode = 0;
static int8_t nightMode = 0;
static int8_t startHour = 22;
static int8_t startMin = 0;
static int8_t endHour = 8;
static int8_t endMin = 0;

static void CheckTime();
static void mqtt_app_stop();
static void mqtt_app_start();

// 保存 wifi 配置参数结构体变量 wifi_config 到 nvs
static void saveWifiConfig(wifi_config_t *wifi_config)
{
    nvs_handle my_handle;
    nvs_open("WIFI_CONFIG", NVS_READWRITE, &my_handle); //打开

    ESP_ERROR_CHECK(nvs_set_blob(my_handle, "wifi_config", wifi_config, sizeof(wifi_config_t)));

    ESP_ERROR_CHECK(nvs_commit(my_handle)); //提交
    nvs_close(my_handle);                   //退出
}

// 从 nvs 中读取wifi配置到给定的 sta_config 结构体变量
static esp_err_t readWifiConfig(wifi_config_t *sta_config)
{
    nvs_handle my_handle;
    nvs_open("WIFI_CONFIG", NVS_READWRITE, &my_handle); //打开

    uint32_t len;
    esp_err_t err = nvs_get_blob(my_handle, "wifi_config", sta_config, &len);

    nvs_close(my_handle); //退出

    return err;
}

// 保存 wifi 配置参数结构体变量 wifi_config 到 nvs
static void saveDeviceConfig()
{
    nvs_handle my_handle;
    nvs_open("DEVICE_CONFIG", NVS_READWRITE, &my_handle); //打开

    ESP_ERROR_CHECK(nvs_set_i8(my_handle, "operateMode", operateMode));
    ESP_ERROR_CHECK(nvs_set_i8(my_handle, "nightMode", nightMode));
    ESP_ERROR_CHECK(nvs_set_i8(my_handle, "startHour", startHour));
    ESP_ERROR_CHECK(nvs_set_i8(my_handle, "startMin", startMin));
    ESP_ERROR_CHECK(nvs_set_i8(my_handle, "endHour", endHour));
    ESP_ERROR_CHECK(nvs_set_i8(my_handle, "endMin", endMin));

    ESP_ERROR_CHECK(nvs_commit(my_handle)); //提交
    nvs_close(my_handle);                   //退出
}

// 从 nvs 中读取wifi配置到给定的 sta_config 结构体变量
static esp_err_t readDeviceConfig()
{
    nvs_handle my_handle;
    nvs_open("DEVICE_CONFIG", NVS_READWRITE, &my_handle); //打开

    esp_err_t err = nvs_get_i8(my_handle, "operateMode", &operateMode);
    err = nvs_get_i8(my_handle, "nightMode", &nightMode);
    err = nvs_get_i8(my_handle, "startHour", &startHour);
    err = nvs_get_i8(my_handle, "startMin", &startMin);
    err = nvs_get_i8(my_handle, "endHour", &endHour);
    err = nvs_get_i8(my_handle, "endMin", &endMin);

    nvs_close(my_handle); //退出
    ESP_LOGI(TAG, "load config: %d %d %d %d %d %d", operateMode, nightMode, startHour, startMin, endHour, endMin);

    return err;
}

static void wifi_event_handler(void *arg, esp_event_base_t event_base,
                               int32_t event_id, void *event_data)
{
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START)
    {
        esp_wifi_connect();
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED)
    {
        ESP_LOGI(TAG, "connect to the AP fail");
        if (WiFiConnection)
        {
            WiFiConnection = false;
            // serial output
            char cmdStr[10];
            ESP_LOGI(TAG, "#5 2");
            sprintf(cmdStr, "#5 2");
            uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
            ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
        }

        if (s_retry_num < max_retry_num)
        {
            esp_wifi_connect();
            s_retry_num++;
            ESP_LOGI(TAG, "retry to connect to the AP");
        }
        else
        {
            if (client)
                mqtt_app_stop();
            vTaskDelay(60 * 1000 / portTICK_PERIOD_MS);
            esp_wifi_connect();
            // xEventGroupSetBits(s_wifi_event_group, WIFI_FAIL_BIT);
        }
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP)
    {
        if (!WiFiConnection)
        {
            WiFiConnection = true;
            // serial output
            char cmdStr[10];
            ESP_LOGI(TAG, "#5 1");
            sprintf(cmdStr, "#5 1");
            uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
            ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
        }
        ip_event_got_ip_t *event = (ip_event_got_ip_t *)event_data;
        ESP_LOGI(TAG, "got ip:" IPSTR, IP2STR(&event->ip_info.ip));
        s_retry_num = 0;
        if (!client)
            mqtt_app_start();
        xEventGroupSetBits(s_wifi_event_group, WIFI_CONNECTED_BIT);
    }
}

static void *_malloc(size_t size)
{
    return heap_caps_malloc(size, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
}

static esp_err_t validate_image_header(esp_app_desc_t *new_app_info)
{
    if (new_app_info == NULL)
    {
        return ESP_ERR_INVALID_ARG;
    }

    const esp_partition_t *running = esp_ota_get_running_partition();
    esp_app_desc_t running_app_info;
    if (esp_ota_get_partition_description(running, &running_app_info) == ESP_OK)
    {
        ESP_LOGI(TAG, "Running firmware version: %s", running_app_info.version);
    }

    if (memcmp(new_app_info->version, running_app_info.version, sizeof(new_app_info->version)) == 0)
    {
        ESP_LOGW(TAG, "Current running version is the same as a new. We will not continue the update.");
        return ESP_FAIL;
    }

    return ESP_OK;
}

static esp_err_t _http_client_init_cb(esp_http_client_handle_t http_client)
{
    esp_err_t err = ESP_OK;
    /* Uncomment to add custom headers to HTTP request */
    // err = esp_http_client_set_header(http_client, "Custom-Header", "Value");
    return err;
}

static void advanced_ota_task(void *pvParameter)
{
    ESP_LOGI(TAG, "Starting Advanced OTA");

    esp_err_t ota_finish_err = ESP_OK;
    esp_http_client_config_t config = {
        .url = Update_SERVER_URL,
        .timeout_ms = 5000,
        .keep_alive_enable = true,
    };

    esp_https_ota_config_t ota_config = {
        .http_config = &config,
        .http_client_init_cb = _http_client_init_cb, // Register a callback to be invoked after esp_http_client is initialized
    };

    esp_https_ota_handle_t https_ota_handle = NULL;
    esp_err_t err = esp_https_ota_begin(&ota_config, &https_ota_handle);
    if (err != ESP_OK)
    {
        ESP_LOGE(TAG, "ESP HTTPS OTA Begin failed");
        vTaskDelete(NULL);
    }

    esp_app_desc_t app_desc;
    err = esp_https_ota_get_img_desc(https_ota_handle, &app_desc);
    if (err != ESP_OK)
    {
        ESP_LOGE(TAG, "esp_https_ota_read_img_desc failed");
        goto ota_end;
    }
    err = validate_image_header(&app_desc);
    if (err != ESP_OK)
    {
        ESP_LOGE(TAG, "image header verification failed");
        goto ota_end;
    }

    while (1)
    {
        err = esp_https_ota_perform(https_ota_handle);
        if (err != ESP_ERR_HTTPS_OTA_IN_PROGRESS)
        {
            break;
        }
        // esp_https_ota_perform returns after every read operation which gives user the ability to
        // monitor the status of OTA upgrade by calling esp_https_ota_get_image_len_read, which gives length of image
        // data read so far.
        ESP_LOGD(TAG, "Image bytes read: %d", esp_https_ota_get_image_len_read(https_ota_handle));
    }

    if (esp_https_ota_is_complete_data_received(https_ota_handle) != true)
    {
        // the OTA image was not completely received and user can customise the response to this situation.
        ESP_LOGE(TAG, "Complete data was not received.");
    }
    else
    {
        ota_finish_err = esp_https_ota_finish(https_ota_handle);
        if ((err == ESP_OK) && (ota_finish_err == ESP_OK))
        {
            ESP_LOGI(TAG, "ESP_HTTPS_OTA upgrade successful. Rebooting ...");
            vTaskDelay(1000 / portTICK_PERIOD_MS);
            if (client)
            {
                esp_mqtt_client_disconnect(client);
            }
            esp_restart();
        }
        else
        {
            if (ota_finish_err == ESP_ERR_OTA_VALIDATE_FAILED)
            {
                ESP_LOGE(TAG, "Image validation failed, image is corrupted");
            }
            ESP_LOGE(TAG, "ESP_HTTPS_OTA upgrade failed 0x%x", ota_finish_err);
            vTaskDelete(NULL);
        }
    }

ota_end:
    esp_https_ota_abort(https_ota_handle);
    ESP_LOGE(TAG, "ESP_HTTPS_OTA upgrade failed");
    vTaskDelete(NULL);
}

static void smartConfig_event_handler(void *arg, esp_event_base_t event_base,
                                      int32_t event_id, void *event_data)
{
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START)
    {
        ESP_LOGI(TAG, "STA Start");
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED)
    {
        esp_wifi_connect();
        xEventGroupClearBits(s_wifi_event_group, CONNECTED_BIT);
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP)
    {
        xEventGroupSetBits(s_wifi_event_group, CONNECTED_BIT);
    }
    else if (event_base == SC_EVENT && event_id == SC_EVENT_SCAN_DONE)
    {
        ESP_LOGI(TAG, "Scan done");
    }
    else if (event_base == SC_EVENT && event_id == SC_EVENT_FOUND_CHANNEL)
    {
        ESP_LOGI(TAG, "Found channel");
    }
    else if (event_base == SC_EVENT && event_id == SC_EVENT_GOT_SSID_PSWD)
    {
        ESP_LOGI(TAG, "Got SSID and password");

        smartconfig_event_got_ssid_pswd_t *evt = (smartconfig_event_got_ssid_pswd_t *)event_data;
        wifi_config_t wifi_config;
        uint8_t ssid[33] = {0};
        uint8_t password[65] = {0};
        uint8_t rvd_data[33] = {0};

        bzero(&wifi_config, sizeof(wifi_config_t));
        memcpy(wifi_config.sta.ssid, evt->ssid, sizeof(wifi_config.sta.ssid));
        memcpy(wifi_config.sta.password, evt->password, sizeof(wifi_config.sta.password));
        wifi_config.sta.bssid_set = evt->bssid_set;
        if (wifi_config.sta.bssid_set == true)
        {
            memcpy(wifi_config.sta.bssid, evt->bssid, sizeof(wifi_config.sta.bssid));
        }

        memcpy(ssid, evt->ssid, sizeof(evt->ssid));
        memcpy(password, evt->password, sizeof(evt->password));
        ESP_LOGI(TAG, "SSID:%s", ssid);
        ESP_LOGI(TAG, "PASSWORD:%s", password);
        if (evt->type == SC_TYPE_ESPTOUCH_V2)
        {
            ESP_ERROR_CHECK(esp_smartconfig_get_rvd_data(rvd_data, sizeof(rvd_data)));
            ESP_LOGI(TAG, "RVD_DATA:");
            for (int i = 0; i < 33; i++)
            {
                printf("%02x ", rvd_data[i]);
            }
            printf("\n");
        }

        ESP_ERROR_CHECK(esp_wifi_disconnect());
        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_STA, &wifi_config));
        saveWifiConfig(&wifi_config);
        esp_wifi_connect();
    }
    else if (event_base == SC_EVENT && event_id == SC_EVENT_SEND_ACK_DONE)
    {
        xEventGroupSetBits(s_wifi_event_group, ESPTOUCH_DONE_BIT);
    }
}
/***************************************************************************************
 * Wi-Fi camera Transfer Implements
 *
 */

camera_fb_t *esp_camera_fb_get()
{
    xEventGroupWaitBits(s_evt_handle, BIT1_NEW_FRAME_START, true, true, portMAX_DELAY);
    ESP_LOGV(TAG, "peek frame = %ld", s_fb.timestamp.tv_sec);
    return &s_fb;
}

void esp_camera_fb_return(camera_fb_t *fb)
{
    ESP_LOGV(TAG, "release frame = %ld", fb->timestamp.tv_sec);
    xEventGroupSetBits(s_evt_handle, BIT2_NEW_FRAME_END);
    return;
}

void jpg_stream_handler(void *arg)
{
    camera_fb_t *fb = NULL;
    esp_err_t res = ESP_OK;
    size_t _jpg_buf_len = 0;
    uint8_t *_jpg_buf = NULL;
    static int64_t last_frame = 0;
    uint16_t times = 3;

    if (uvc_streaming_resume() != ESP_OK)
    {
        uvc_streaming_suspend();
        ESP_LOGI(TAG, "xTaskDeleteDone!");
        vTaskDelete(NULL);
    }

    if (!last_frame)
    {
        last_frame = esp_timer_get_time();
    }

    while (times--)
    {

        fb = esp_camera_fb_get();

        if (!fb)
        {
            ESP_LOGE(TAG, "Camera capture failed");
            res = ESP_FAIL;
            break;
        }
        else
        {
            _jpg_buf_len = fb->len;
            _jpg_buf = fb->buf;
            ESP_LOGI(TAG, "_jpg_buf_len:%d", _jpg_buf_len);
        }

        if (res == ESP_OK && times == 0)
        {
            size_t out;
            unsigned char *tempData = (unsigned char *)calloc(32768, sizeof(unsigned char));
            int ret = mbedtls_base64_encode(tempData, 32768, &out, _jpg_buf, _jpg_buf_len);
            if (ret != 0)
            {
                ESP_LOGE(TAG, "Error in mbedtls encode! ret = -0x%x", -ret);
            }
            // ESP_LOGI(TAG, "tempData: %d %s ", out, tempData);

            cJSON *pRoot = cJSON_CreateObject();
            cJSON_AddStringToObject(pRoot, "dataType", "2");
            cJSON_AddStringToObject(pRoot, "frame", (char *)tempData);
            char *sendData = cJSON_Print(pRoot); // 从cJSON对象中获取有格式的JSON对象
            // ESP_LOGI(TAG, "data:%s", sendData);
            char topic[50];
            sprintf(topic, "topic/%s/data", MQTT_CLIENT_ID);
            esp_mqtt_client_publish(client, topic, sendData, 0, 0, true); // publish data
            free(tempData);
            cJSON_free((void *)sendData); // 释放cJSON_Print ()分配出来的内存空间
            cJSON_Delete(pRoot);          // 释放cJSON_CreateObject ()分配出来的内存
        }

        if (fb)
        {
            esp_camera_fb_return(fb);
            fb = NULL;
            _jpg_buf = NULL;
        }
        else if (_jpg_buf)
        {
            _jpg_buf = NULL;
        }

        int64_t fr_end = esp_timer_get_time();
        int64_t frame_time = fr_end - last_frame;
        last_frame = fr_end;
        frame_time /= 1000;
        ESP_LOGI(TAG, "MJPG: %uB %ums (%.1ffps)",
                 (uint32_t)(_jpg_buf_len),
                 (uint32_t)frame_time, 1000.0 / (uint32_t)frame_time);
    }

    last_frame = 0;
    uvc_streaming_suspend();
    ESP_LOGI(TAG, "xTaskDeleteDone!");
    vTaskDelete(NULL);
}

/* *******************************************************************************************
 * This callback function runs once per frame. Use it to perform any
 * quick processing you need, or have it put the frame into your application's
 * input queue. If this function takes too long, you'll start losing frames. */
static void frame_cb(uvc_frame_t *frame, void *ptr)
{
    ESP_LOGV(TAG, "callback! frame_format = %d, seq = %u, width = %d, height = %d, length = %u, ptr = %d",
             frame->frame_format, frame->sequence, frame->width, frame->height, frame->data_bytes, (int)ptr);

    switch (frame->frame_format)
    {
    case UVC_FRAME_FORMAT_MJPEG:
        s_fb.buf = frame->data;
        s_fb.len = frame->data_bytes;
        s_fb.width = frame->width;
        s_fb.height = frame->height;
        s_fb.format = PIXFORMAT_JPEG;
        s_fb.timestamp.tv_sec = frame->sequence;
        xEventGroupSetBits(s_evt_handle, BIT1_NEW_FRAME_START);
        ESP_LOGV(TAG, "send frame = %u", frame->sequence);
        xEventGroupWaitBits(s_evt_handle, BIT2_NEW_FRAME_END, true, true, pdTICKS_TO_MS(1000));
        ESP_LOGV(TAG, "send frame done = %u", frame->sequence);
        break;
    default:
        ESP_LOGW(TAG, "Format not supported");
        assert(0);
        break;
    }
}

static void uvc_streaming_init()
{
    /* create eventgroup for task sync */
    s_evt_handle = xEventGroupCreate();
    if (s_evt_handle == NULL)
    {
        ESP_LOGE(TAG, "line-%u event group create faild", __LINE__);
        assert(0);
    }

    /* malloc double buffer for usb payload, xfer_buffer_size >= frame_buffer_size*/
    uint8_t *xfer_buffer_a = (uint8_t *)_malloc(UVC_XFER_BUFFER_SIZE);
    assert(xfer_buffer_a != NULL);
    uint8_t *xfer_buffer_b = (uint8_t *)_malloc(UVC_XFER_BUFFER_SIZE);
    assert(xfer_buffer_b != NULL);

    /* malloc frame buffer for a jpeg frame*/
    uint8_t *frame_buffer = (uint8_t *)_malloc(UVC_XFER_BUFFER_SIZE);
    assert(frame_buffer != NULL);

    /* the quick demo skip the standred get descriptors process,
    users need to get params from camera descriptors from PC side,
    eg. run `lsusb -v` in linux, then modify related MACROS */
    uvc_config_t uvc_config = {
        .dev_speed = USB_SPEED_FULL,
        .configuration = DESCRIPTOR_CONFIGURATION_INDEX,
        .format_index = DESCRIPTOR_FORMAT_MJPEG_INDEX,
        .frame_width = UVC_FRAME_WIDTH,
        .frame_height = UVC_FRAME_HEIGHT,
        .frame_index = UVC_FRAME_INDEX,
        .frame_interval = UVC_FRAME_INTERVAL,
        .interface = DESCRIPTOR_STREAM_INTERFACE_INDEX,
        .interface_alt = UVC_ISOC_INTERFACE_ALT,
        .isoc_ep_addr = DESCRIPTOR_STREAM_ISOC_ENDPOINT_ADDR,
        .isoc_ep_mps = UVC_ISOC_EP_MPS,
        .xfer_buffer_size = UVC_XFER_BUFFER_SIZE,
        .xfer_buffer_a = xfer_buffer_a,
        .xfer_buffer_b = xfer_buffer_b,
        .frame_buffer_size = UVC_XFER_BUFFER_SIZE,
        .frame_buffer = frame_buffer,
    };

    /* pre-config UVC driver with params from known USB Camera Descriptors*/
    esp_err_t ret = uvc_streaming_config(&uvc_config);

    /* Start camera IN stream with pre-configs, uvc driver will create multi-tasks internal
    to handle usb data from different pipes, and user's callback will be called after new frame ready. */
    if (ret != ESP_OK)
    {
        ESP_LOGE(TAG, "uvc streaming config failed");
    }
    else
    {
        uvc_streaming_start(frame_cb, NULL);
        uvc_streaming_suspend();
    }
}

static void base_wifi_init()
{
    s_wifi_event_group = xEventGroupCreate();
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_create_default_wifi_sta();
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));
    ESP_ERROR_CHECK(esp_event_handler_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler, NULL));
    ESP_ERROR_CHECK(esp_event_handler_register(IP_EVENT, IP_EVENT_STA_GOT_IP, &wifi_event_handler, NULL));

    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_STA));
    ESP_ERROR_CHECK(esp_wifi_set_config(ESP_IF_WIFI_STA, &s_wifi_config));
    ESP_ERROR_CHECK(esp_wifi_start());

    /* Waiting until either the connection is established (WIFI_CONNECTED_BIT) or connection failed for the maximum
     * number of re-tries (WIFI_FAIL_BIT). The bits are set by wifi_event_handler() (see above) */
    EventBits_t bits = xEventGroupWaitBits(s_wifi_event_group,
                                           WIFI_CONNECTED_BIT | WIFI_FAIL_BIT,
                                           pdFALSE,
                                           pdFALSE,
                                           portMAX_DELAY);
    /* xEventGroupWaitBits() returns the bits before the call returned, hence we can test which event actually
     * happened. */
    if (bits & WIFI_CONNECTED_BIT)
    {
        ESP_LOGI(TAG, "connected to ap SSID:%s password:%s",
                 s_wifi_config.sta.ssid, s_wifi_config.sta.password);
    }
    else if (bits & WIFI_FAIL_BIT)
    {
        ESP_LOGI(TAG, "Failed to connect to SSID:%s, password:%s",
                 s_wifi_config.sta.ssid, s_wifi_config.sta.password);
    }
    else
    {
        ESP_LOGE(TAG, "UNEXPECTED EVENT");
    }

    /* The event will not be processed after unregister */
    // ESP_ERROR_CHECK(esp_event_handler_unregister(IP_EVENT, IP_EVENT_STA_GOT_IP, &wifi_event_handler));
    // ESP_ERROR_CHECK(esp_event_handler_unregister(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler));
    // vEventGroupDelete(s_wifi_event_group);
}

static void smartConfig_init(void)
{
    ESP_ERROR_CHECK(esp_netif_init());
    s_wifi_event_group = xEventGroupCreate();
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_t *sta_netif = esp_netif_create_default_wifi_sta();
    assert(sta_netif);

    wifi_init_config_t wifi_cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&wifi_cfg));

    ESP_ERROR_CHECK(esp_event_handler_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &smartConfig_event_handler, NULL));
    ESP_ERROR_CHECK(esp_event_handler_register(IP_EVENT, IP_EVENT_STA_GOT_IP, &smartConfig_event_handler, NULL));
    ESP_ERROR_CHECK(esp_event_handler_register(SC_EVENT, ESP_EVENT_ANY_ID, &smartConfig_event_handler, NULL));

    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_STA));
    ESP_ERROR_CHECK(esp_wifi_start());

    EventBits_t uxBits;
    ESP_ERROR_CHECK(esp_smartconfig_set_type(SC_TYPE_ESPTOUCH_AIRKISS));
    smartconfig_start_config_t sc_cfg = SMARTCONFIG_START_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_smartconfig_start(&sc_cfg));
    while (1)
    {
        uxBits = xEventGroupWaitBits(s_wifi_event_group, CONNECTED_BIT | ESPTOUCH_DONE_BIT, true, false, portMAX_DELAY);
        if (uxBits & CONNECTED_BIT)
        {
            ESP_LOGI(TAG, "WiFi Connected to ap");
        }
        if (uxBits & ESPTOUCH_DONE_BIT)
        {
            ESP_LOGI(TAG, "smartconfig over");
            esp_smartconfig_stop();
            break;
        }
    }
}

static void wifi_init()
{
    if (readWifiConfig(&s_wifi_config) == ESP_OK)
    {
        base_wifi_init();
    }
    else
    {
        smartConfig_init();
        esp_restart();
    }
}

static void log_error_if_nonzero(const char *message, int error_code)
{
    if (error_code != 0)
    {
        ESP_LOGE(TAG, "Last error %s: 0x%x", message, error_code);
    }
}

void send_device_data(char *sendType)
{
    cJSON *pRoot = cJSON_CreateObject();
    char tempData[10];
    cJSON_AddStringToObject(pRoot, "dataType", "1");
    cJSON_AddStringToObject(pRoot, "sendType", sendType);
    sprintf(tempData, "%d", temp);
    cJSON_AddStringToObject(pRoot, "temp", tempData);
    sprintf(tempData, "%d", humi);
    cJSON_AddStringToObject(pRoot, "humi", tempData);
    sprintf(tempData, "%.1f", lux);
    cJSON_AddStringToObject(pRoot, "lux", tempData);
    sprintf(tempData, "%d", weight);
    cJSON_AddStringToObject(pRoot, "weight", tempData);
    sprintf(tempData, "%.2f", soilTemp);
    cJSON_AddStringToObject(pRoot, "soilTemp", tempData);
    sprintf(tempData, "%.2f", soilHumi);
    cJSON_AddStringToObject(pRoot, "soilHumi", tempData);
    sprintf(tempData, "%d", soilEC);
    cJSON_AddStringToObject(pRoot, "soilEC", tempData);
    sprintf(tempData, "%.1f", soilPH);
    cJSON_AddStringToObject(pRoot, "soilPH", tempData);
    sprintf(tempData, "%d", waterHeight);
    cJSON_AddStringToObject(pRoot, "waterHeight", tempData);
    sprintf(tempData, "%d", light_pwm);
    cJSON_AddStringToObject(pRoot, "light", tempData);
    sprintf(tempData, "%d", fan_pwm);
    cJSON_AddStringToObject(pRoot, "fan", tempData);
    sprintf(tempData, "%d", waterPump_pwm);
    cJSON_AddStringToObject(pRoot, "waterPump", tempData);
    sprintf(tempData, "%d", operateMode);
    cJSON_AddStringToObject(pRoot, "operateMode", tempData);
    sprintf(tempData, "%d", nightMode);
    cJSON_AddStringToObject(pRoot, "nightMode", tempData);
    sprintf(tempData, "%d", startHour);
    cJSON_AddStringToObject(pRoot, "startHour", tempData);
    sprintf(tempData, "%d", startMin);
    cJSON_AddStringToObject(pRoot, "startMin", tempData);
    sprintf(tempData, "%d", endHour);
    cJSON_AddStringToObject(pRoot, "endHour", tempData);
    sprintf(tempData, "%d", endMin);
    cJSON_AddStringToObject(pRoot, "endMin", tempData);
    char *sendData = cJSON_Print(pRoot); // 从cJSON对象中获取有格式的JSON对象
    ESP_LOGI(TAG, "data:%s", sendData);  // 打印数据
    char topic[50];
    sprintf(topic, "topic/%s/data", MQTT_CLIENT_ID);
    esp_mqtt_client_publish(client, topic, sendData, 0, 0, true); // publish data
    cJSON_free((void *)sendData);                                 // 释放cJSON_Print ()分配出来的内存空间
    cJSON_Delete(pRoot);                                          // 释放cJSON_CreateObject ()分配出来的内存
}

/*
 * @brief Event handler registered to receive MQTT events
 *
 *  This function is called by the MQTT client event loop.
 *
 * @param handler_args user data registered to the event.
 * @param base Event base for the handler(always MQTT Base in this example).
 * @param event_id The id for the received event.
 * @param event_data The data for the event, esp_mqtt_event_handle_t.
 */
static void mqtt_event_handler(void *handler_args, esp_event_base_t base, int32_t event_id, void *event_data)
{
    ESP_LOGD(TAG, "Event dispatched from event loop base=%s, event_id=%d", base, event_id);
    esp_mqtt_event_handle_t event = event_data;
    esp_mqtt_client_handle_t client = event->client;

    switch ((esp_mqtt_event_id_t)event_id)
    {
    case MQTT_EVENT_CONNECTED:
        ESP_LOGI(TAG, "MQTT_EVENT_CONNECTED");
        char topic[50];
        sprintf(topic, "topic/%s/active", MQTT_CLIENT_ID);
        esp_mqtt_client_subscribe(client, topic, 1);
        sprintf(topic, "topic/%s/cmd", MQTT_CLIENT_ID);
        esp_mqtt_client_subscribe(client, topic, 1);
        break;
    case MQTT_EVENT_DISCONNECTED:
        ESP_LOGE(TAG, "MQTT_EVENT_DISCONNECTED");
        break;
    case MQTT_EVENT_SUBSCRIBED:
        ESP_LOGI(TAG, "MQTT_EVENT_SUBSCRIBED, msg_id=%d", event->msg_id);
        break;
    case MQTT_EVENT_UNSUBSCRIBED:
        ESP_LOGI(TAG, "MQTT_EVENT_UNSUBSCRIBED, msg_id=%d", event->msg_id);
        break;
    case MQTT_EVENT_PUBLISHED:
        ESP_LOGI(TAG, "MQTT_EVENT_PUBLISHED, msg_id=%d", event->msg_id);
        break;
    case MQTT_EVENT_DATA:
        ESP_LOGI(TAG, "MQTT_EVENT_DATA");
        printf("TOPIC=%.*s\r\n", event->topic_len, event->topic);
        printf("DATA=%.*s\r\n", event->data_len, event->data);

        cJSON *pJsonRoot = cJSON_Parse(event->data);
        if (pJsonRoot != NULL)
        {
            if (strstr(event->topic, "cmd"))
            {
                cJSON *pUID = cJSON_GetObjectItem(pJsonRoot, "uid"); // 解析指定字段字符串内容
                if (cJSON_IsString(pUID))
                {
                    if (!strcmp(UID, pUID->valuestring))
                    {
                        userOnlineStatus = true;
                        cJSON *pCMD = cJSON_GetObjectItem(pJsonRoot, "cmd"); // 解析指定字段字符串内容
                        if (cJSON_IsString(pCMD))                            // 判断mac字段是否string类型
                        {
                            if (!strcmp(pCMD->valuestring, "1"))
                            {
                                send_device_data("1");
                            }
                            else if (!strcmp(pCMD->valuestring, "2"))
                            {

                                TaskHandle_t xHandle = xTaskGetHandle("JPG_STREAM");
                                if (xHandle == NULL)
                                {
                                    xTaskCreatePinnedToCore(jpg_stream_handler, "JPG_STREAM", 30 * 1024, NULL, 5, NULL, 1);
                                    ESP_LOGI(TAG, "xTaskCreateDone!");
                                }
                            }
                            else if (!strcmp(pCMD->valuestring, "3"))
                            {
                                cJSON *pData = cJSON_GetObjectItem(pJsonRoot, "data"); // 解析指定字段字符串内容
                                if (cJSON_IsString(pData))
                                {
                                    light_pwm = atoi(pData->valuestring);
                                    // serial output
                                    char cmdStr[10];
                                    ESP_LOGI(TAG, "#1 %03d", light_pwm);
                                    sprintf(cmdStr, "#1 %03d", light_pwm);
                                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                                }
                            }
                            else if (!strcmp(pCMD->valuestring, "4"))
                            {
                                cJSON *pData = cJSON_GetObjectItem(pJsonRoot, "data"); // 解析指定字段字符串内容
                                if (cJSON_IsString(pData))
                                {
                                    fan_pwm = atoi(pData->valuestring);
                                    // serial output
                                    char cmdStr[10];
                                    ESP_LOGI(TAG, "#2 %03d", fan_pwm);
                                    sprintf(cmdStr, "#2 %03d", fan_pwm);
                                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                                }
                            }
                            else if (!strcmp(pCMD->valuestring, "5"))
                            {
                                cJSON *pData = cJSON_GetObjectItem(pJsonRoot, "data"); // 解析指定字段字符串内容
                                if (cJSON_IsString(pData))
                                {
                                    waterPump_pwm = atoi(pData->valuestring);
                                    // serial output
                                    char cmdStr[10];
                                    ESP_LOGI(TAG, "#3 %03d", waterPump_pwm);
                                    sprintf(cmdStr, "#3 %03d", waterPump_pwm);
                                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                                }
                            }
                            else if (!strcmp(pCMD->valuestring, "6"))
                            {
                                cJSON *pData = cJSON_GetObjectItem(pJsonRoot, "data"); // 解析指定字段字符串内容
                                if (cJSON_IsString(pData))
                                {
                                    operateMode = atoi(pData->valuestring);
                                    // serial output
                                    char cmdStr[10];
                                    ESP_LOGI(TAG, "#6 %d", operateMode);
                                    sprintf(cmdStr, "#6 %d", operateMode);
                                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                                    saveDeviceConfig();
                                }
                            }
                            else if (!strcmp(pCMD->valuestring, "7"))
                            {
                                cJSON *pData = cJSON_GetObjectItem(pJsonRoot, "data"); // 解析指定字段字符串内容
                                if (cJSON_IsString(pData))
                                {
                                    if (pData->valuestring[0] == '0')
                                    {
                                        nightMode = 0;
                                    }
                                    else if (pData->valuestring[0] == '1')
                                    {
                                        nightMode = 1;
                                    }
                                    else if (pData->valuestring[0] == '2')
                                    {
                                        char tempStr[3];
                                        memcpy(tempStr, &pData->valuestring[2], 2);
                                        tempStr[2] = '\0';
                                        startHour = atoi(tempStr);
                                        memcpy(tempStr, &pData->valuestring[5], 2);
                                        tempStr[2] = '\0';
                                        startMin = atoi(tempStr);
                                        memcpy(tempStr, &pData->valuestring[8], 2);
                                        tempStr[2] = '\0';
                                        endHour = atoi(tempStr);
                                        memcpy(tempStr, &pData->valuestring[11], 2);
                                        tempStr[2] = '\0';
                                        endMin = atoi(tempStr);
                                    }
                                    saveDeviceConfig();
                                    CheckTime();
                                }
                            }
                        }
                    }
                }
            }
            else if (strstr(event->topic, "active"))
            {
                cJSON *pUID = cJSON_GetObjectItem(pJsonRoot, "uid"); // 解析指定字段字符串内容
                if (cJSON_IsString(pUID))
                {
                    if (strlen(pUID->valuestring) > 0)
                    {
                        strcpy(UID, pUID->valuestring);
                        char topic[100];
                        sprintf(topic, "$SYS/brokers/emqx@aliyun/clients/%s/#", UID);
                        esp_mqtt_client_subscribe(client, topic, 1);
                    }
                    else
                    {
                        if (strlen(UID) > 0)
                        {
                            char topic[100];
                            sprintf(topic, "$SYS/brokers/emqx@aliyun/clients/%s/#", UID);
                            esp_mqtt_client_unsubscribe(client, topic);
                            UID[0] = '\0';
                        }
                    }
                }
            }
            else if (strstr(event->topic, "/connected"))
            {
                userOnlineStatus = true;
                send_device_data("2");
            }
            else if (strstr(event->topic, "/disconnected"))
            {
                userOnlineStatus = false;
            }
            cJSON_Delete(pJsonRoot); // 释放cJSON_Parse()分配出来的内存空间
        }
        break;
    case MQTT_EVENT_ERROR:
        ESP_LOGI(TAG, "MQTT_EVENT_ERROR");
        if (event->error_handle->error_type == MQTT_ERROR_TYPE_TCP_TRANSPORT)
        {
            log_error_if_nonzero("reported from esp-tls", event->error_handle->esp_tls_last_esp_err);
            log_error_if_nonzero("reported from tls stack", event->error_handle->esp_tls_stack_err);
            log_error_if_nonzero("captured as transport's socket errno", event->error_handle->esp_transport_sock_errno);
            ESP_LOGI(TAG, "Last errno string (%s)", strerror(event->error_handle->esp_transport_sock_errno));
        }
        break;
    default:
        ESP_LOGI(TAG, "Other event id:%d", event->event_id);
        break;
    }
}

void ReportTask(void *arg)
{
    TickType_t xLastWakeTime;
    const TickType_t xDelayXms = pdMS_TO_TICKS(30 * 60 * 1000);
    xLastWakeTime = xTaskGetTickCount();

    while (1)
    {
        vTaskDelayUntil(&xLastWakeTime, xDelayXms);
        ESP_LOGI(TAG, "ReportTask Run");
        send_device_data("3");
    }
    vTaskDelete(NULL);
}

static void mqtt_app_start()
{
    esp_mqtt_client_config_t mqtt_cfg = {
        .uri = MQTT_BROKER_URL,
        .client_id = MQTT_CLIENT_ID,
        .username = MQTT_CLIENT_ID,
        .keepalive = 60,
    };

    client = esp_mqtt_client_init(&mqtt_cfg);
    /* The last argument may be used to pass data to the event handler, in this example mqtt_event_handler */
    esp_mqtt_client_register_event(client, ESP_EVENT_ANY_ID, mqtt_event_handler, NULL);
    esp_mqtt_client_start(client);
    xTaskCreate(ReportTask, "DataReport", 8 * 1024, NULL, 5, NULL);
}

static void mqtt_app_stop()
{
    TaskHandle_t xHandle = xTaskGetHandle("DataReport");
    if (xHandle != NULL)
    {
        vTaskDelete(xHandle);
        ESP_LOGI(TAG, "xTaskDeleteDone!");
    }
    esp_mqtt_client_stop(client);
    esp_mqtt_client_destroy(client);
    client = NULL;
}

static void uart_event_task(void *pvParameters)
{
    uart_event_t event;
    size_t buffered_size;
    uint8_t *dtmp = (uint8_t *)malloc(RD_BUF_SIZE);
    while (1)
    {
        // Waiting for UART event.
        if (xQueueReceive(uart1_queue, (void *)&event, (portTickType)portMAX_DELAY))
        {
            bzero(dtmp, RD_BUF_SIZE);
            ESP_LOGI(TAG, "uart[%d] event:", EX_UART_NUM);
            switch (event.type)
            {
            // Event of UART receving data
            /*We'd better handler data event fast, there would be much more data events than
            other types of events. If we take too much time on data event, the queue might
            be full.*/
            case UART_DATA:
                ESP_LOGI(TAG, "[UART DATA Length]: %d", event.size);
                uart_read_bytes(EX_UART_NUM, dtmp, event.size, portMAX_DELAY);
                ESP_LOGI(TAG, "[UART DATA]: %s", dtmp);
                if (dtmp[1] == 0x31 && event.size == 65)
                {
                    char tempIStr[6], tempfStr[3];
                    memcpy(tempIStr, &dtmp[3], 5);
                    tempIStr[5] = '\0';
                    memcpy(tempfStr, &dtmp[9], 1);
                    tempfStr[1] = '\0';
                    lux = atoi(tempIStr) + atoi(tempfStr) * 0.1;
                    memcpy(tempIStr, &dtmp[11], 2);
                    tempIStr[2] = '\0';
                    temp = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[14], 2);
                    tempIStr[2] = '\0';
                    humi = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[17], 5);
                    tempIStr[5] = '\0';
                    weight = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[23], 2);
                    tempIStr[2] = '\0';
                    memcpy(tempfStr, &dtmp[26], 2);
                    tempfStr[2] = '\0';
                    soilTemp = atoi(tempIStr) + atoi(tempfStr) * 0.01;
                    memcpy(tempIStr, &dtmp[29], 2);
                    tempIStr[2] = '\0';
                    memcpy(tempfStr, &dtmp[32], 2);
                    tempfStr[2] = '\0';
                    soilHumi = atoi(tempIStr) + atoi(tempfStr) * 0.01;
                    memcpy(tempIStr, &dtmp[35], 5);
                    tempIStr[5] = '\0';
                    soilEC = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[41], 2);
                    tempIStr[2] = '\0';
                    memcpy(tempfStr, &dtmp[44], 1);
                    tempfStr[1] = '\0';
                    soilPH = atoi(tempIStr) + atoi(tempfStr) * 0.1;
                    memcpy(tempIStr, &dtmp[46], 5);
                    tempIStr[5] = '\0';
                    waterHeight = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[52], 3);
                    tempIStr[3] = '\0';
                    light_pwm = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[56], 3);
                    tempIStr[3] = '\0';
                    fan_pwm = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[60], 3);
                    tempIStr[3] = '\0';
                    waterPump_pwm = atoi(tempIStr);
                    memcpy(tempIStr, &dtmp[64], 1);
                    tempIStr[1] = '\0';
                    operateMode = atoi(tempIStr);
                    saveDeviceConfig();
                }
                else if (dtmp[1] == 0x32 && event.size == 4)
                {
                    if (dtmp[3] == 0x31)
                    {
                        // clean config
                        ESP_ERROR_CHECK(nvs_flash_erase());
                        if (client)
                        {
                            esp_mqtt_client_disconnect(client);
                        }
                        esp_restart();
                    }
                    else if (dtmp[3] == 0x32)
                    {
                        if (client)
                        {
                            esp_mqtt_client_disconnect(client);
                        }
                        esp_restart();
                    }
                }
                break;
            // Event of HW FIFO overflow detected
            case UART_FIFO_OVF:
                ESP_LOGI(TAG, "hw fifo overflow");
                // If fifo overflow happened, you should consider adding flow control for your application.
                // The ISR has already reset the rx FIFO,
                // As an example, we directly flush the rx buffer here in order to read more data.
                uart_flush_input(EX_UART_NUM);
                xQueueReset(uart1_queue);
                break;
            // Event of UART ring buffer full
            case UART_BUFFER_FULL:
                ESP_LOGI(TAG, "ring buffer full");
                // If buffer full happened, you should consider encreasing your buffer size
                // As an example, we directly flush the rx buffer here in order to read more data.
                uart_flush_input(EX_UART_NUM);
                xQueueReset(uart1_queue);
                break;
            // Event of UART RX break detected
            case UART_BREAK:
                ESP_LOGI(TAG, "uart rx break");
                break;
            // Event of UART parity check error
            case UART_PARITY_ERR:
                ESP_LOGI(TAG, "uart parity error");
                break;
            // Event of UART frame error
            case UART_FRAME_ERR:
                ESP_LOGI(TAG, "uart frame error");
                break;
            // UART_PATTERN_DET
            case UART_PATTERN_DET:
                uart_get_buffered_data_len(EX_UART_NUM, &buffered_size);
                int pos = uart_pattern_pop_pos(EX_UART_NUM);
                ESP_LOGI(TAG, "[UART PATTERN DETECTED] pos: %d, buffered size: %d", pos, buffered_size);
                if (pos == -1)
                {
                    // There used to be a UART_PATTERN_DET event, but the pattern position queue is full so that it can not
                    // record the position. We should set a larger queue size.
                    // As an example, we directly flush the rx buffer here.
                    uart_flush_input(EX_UART_NUM);
                }
                else
                {
                    uart_read_bytes(EX_UART_NUM, dtmp, pos, 100 / portTICK_PERIOD_MS);
                    uint8_t pat[PATTERN_CHR_NUM + 1];
                    memset(pat, 0, sizeof(pat));
                    uart_read_bytes(EX_UART_NUM, pat, PATTERN_CHR_NUM, 100 / portTICK_PERIOD_MS);
                    ESP_LOGI(TAG, "read data: %s", dtmp);
                    ESP_LOGI(TAG, "read pat : %s", pat);
                }
                break;
            // Others
            default:
                ESP_LOGI(TAG, "uart event type: %d", event.type);
                break;
            }
        }
    }
    free(dtmp);
    dtmp = NULL;
    vTaskDelete(NULL);
}

static void uart_init()
{
    uart_config_t uart_config = {
        .baud_rate = 115200,
        .data_bits = UART_DATA_8_BITS,
        .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
        .source_clk = UART_SCLK_APB,
    };
    // Install UART driver, and get the queue.
    uart_driver_install(EX_UART_NUM, BUF_SIZE * 2, BUF_SIZE * 2, 100, &uart1_queue, 0);
    uart_param_config(EX_UART_NUM, &uart_config);

    // Set UART pins (using UART1 default pins ie no changes.)
    uart_set_pin(EX_UART_NUM, UART1TX_PIN, UART1RX_PIN, UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE);

    // Set uart pattern detect function.
    // uart_enable_pattern_det_baud_intr(EX_UART_NUM, '#', PATTERN_CHR_NUM, 9, 0, 0);
    // Reset the pattern queue length to record at most 20 pattern positions.
    // uart_pattern_queue_reset(EX_UART_NUM, 80);

    uart_write_bytes_with_break(EX_UART_NUM, " start ", 7, 100);
    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));

    // Create a task to handler UART event from ISR
    xTaskCreate(uart_event_task, "uart_event_task", 8 * 1024, NULL, 12, NULL);
}

void ota_init()
{
#if defined(CONFIG_BOOTLOADER_APP_ROLLBACK_ENABLE)
    /**
     * We are treating successful WiFi connection as a checkpoint to cancel rollback
     * process and mark newly updated firmware image as active. For production cases,
     * please tune the checkpoint behavior per end application requirement.
     */
    const esp_partition_t *running = esp_ota_get_running_partition();
    esp_ota_img_states_t ota_state;
    if (esp_ota_get_state_partition(running, &ota_state) == ESP_OK)
    {
        if (ota_state == ESP_OTA_IMG_PENDING_VERIFY)
        {
            if (esp_ota_mark_app_valid_cancel_rollback() == ESP_OK)
            {
                ESP_LOGI(TAG, "App is valid, rollback cancelled successfully");
            }
            else
            {
                ESP_LOGE(TAG, "Failed to cancel rollback");
            }
        }
    }
#endif
    xTaskCreate(&advanced_ota_task, "advanced_ota_task", 8 * 1024, NULL, 8, NULL);
}

void send_info()
{
    readDeviceConfig();
    /* Get CID Form MAC */
    esp_efuse_mac_get_default(MAC);
    sprintf(CID, "%02X%02X%02X", MAC[3], MAC[4], MAC[5]);
    strcpy(MQTT_CLIENT_ID, "Farm_");
    strcat(MQTT_CLIENT_ID, CID);
    ESP_LOGI(TAG, "MQTT_CLIENT_ID:%s", MQTT_CLIENT_ID);
    // serial output
    char cmdStr[25];
    ESP_LOGI(TAG, "#4 %s", MQTT_CLIENT_ID);
    sprintf(cmdStr, "#4 %s", MQTT_CLIENT_ID);
    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
    ESP_LOGI(TAG, "#5 2");
    sprintf(cmdStr, "#5 2");
    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
}

void time_sync_notification_cb(struct timeval *tv)
{
    ESP_LOGI(TAG, "Notification of a time synchronization event");
}

static void obtain_time(void)
{
    ESP_LOGI(TAG, "Initializing SNTP");
    sntp_setoperatingmode(SNTP_OPMODE_POLL);
    sntp_setservername(0, "ntp.aliyun.com");
    sntp_setservername(1, "cn.pool.ntp.org");
    sntp_setservername(2, "time1.cloud.tencent.com");
    sntp_set_time_sync_notification_cb(time_sync_notification_cb);
    sntp_init();
    // wait for time to be set
    int retry = 0;
    const int retry_count = 10;
    while (sntp_get_sync_status() == SNTP_SYNC_STATUS_RESET && ++retry < retry_count)
    {
        ESP_LOGI(TAG, "Waiting for system time to be set... (%d/%d)", retry, retry_count);
        vTaskDelay(2000 / portTICK_PERIOD_MS);
    }
    if (retry >= retry_count)
    {
        ESP_LOGE(TAG, "Sync Time error!");
        esp_restart();
    }
}

static void CheckTime()
{
    time_t now;
    struct tm timeinfo;
    char strftime_buf[64];
    time(&now);
    localtime_r(&now, &timeinfo);

    strftime(strftime_buf, sizeof(strftime_buf), "%c", &timeinfo);
    ESP_LOGI(TAG, "The current date/time in Shanghai is: %s", strftime_buf);
    ESP_LOGI(TAG, "operateMode: %d nightMode: %d", operateMode, nightMode);
    if (nightMode)
    {
        int startTime = startHour * 60 + startMin;
        int endTime = endHour * 60 + endMin;
        int currentTime = timeinfo.tm_hour * 60 + timeinfo.tm_min;
        ESP_LOGI(TAG, "ST: %d:%d ET: %d:%d CT: %d:%d LastMute: %d", startHour, startMin, endHour, endMin, timeinfo.tm_hour, timeinfo.tm_min, mute);
        if (startTime > endTime)
        {
            if ((currentTime >= startTime) || (currentTime <= endTime))
            {
                if (mute != 1)
                {
                    mute = 1;
                    // serial output
                    char cmdStr[10];
                    ESP_LOGI(TAG, "#7 0");
                    sprintf(cmdStr, "#7 0");
                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                }
            }
            else
            {
                if (mute != 0)
                {
                    mute = 0;
                    // serial output
                    char cmdStr[10];
                    ESP_LOGI(TAG, "#7 1");
                    sprintf(cmdStr, "#7 1");
                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                }
            }
        }
        else
        {
            if ((currentTime >= startTime) && (currentTime <= endTime))
            {
                if (mute != 1)
                {
                    mute = 1;
                    // serial output
                    char cmdStr[10];
                    ESP_LOGI(TAG, "#7 0");
                    sprintf(cmdStr, "#7 0");
                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                }
            }
            else
            {
                if (mute != 0)
                {
                    mute = 0;
                    // serial output
                    char cmdStr[10];
                    ESP_LOGI(TAG, "#7 1");
                    sprintf(cmdStr, "#7 1");
                    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
                    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
                }
            }
        }
    }
    else
    {
        if (mute != 0)
        {
            mute = 0;
            // serial output
            char cmdStr[10];
            ESP_LOGI(TAG, "#7 1");
            sprintf(cmdStr, "#7 1");
            uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
            ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
        }
    }
    ESP_LOGI(TAG, "NowMute: %d", mute);
}

void TimeTask(void *arg)
{
    TickType_t xLastWakeTime;
    const TickType_t xDelayXms = pdMS_TO_TICKS(60 * 1000);
    time_t now;
    struct tm timeinfo;
    time(&now);
    localtime_r(&now, &timeinfo);
    if (timeinfo.tm_sec != 0)
        vTaskDelay((60 - timeinfo.tm_sec) * 1000 / portTICK_PERIOD_MS);
    xLastWakeTime = xTaskGetTickCount();

    while (1)
    {
        vTaskDelayUntil(&xLastWakeTime, xDelayXms);
        ESP_LOGI(TAG, "TimeTask Run");
        CheckTime();
    }
    vTaskDelete(NULL);
}

static void time_init()
{
    time_t now;
    struct tm timeinfo;
    time(&now);
    localtime_r(&now, &timeinfo);
    // Is time set? If not, tm_year will be (1970 - 1900).
    if (timeinfo.tm_year < (2021 - 1900))
    {
        ESP_LOGI(TAG, "Time is not set yet. Connecting to WiFi and getting time over NTP.");
        obtain_time();
    }

    // Set timezone to China Standard Time
    setenv("TZ", "CST-8", 1);
    tzset();
    xTaskCreate(TimeTask, "TimeControl", 8 * 1024, NULL, 5, NULL);
}

static void send_mode()
{
    CheckTime();
    // serial output
    char cmdStr[10];
    ESP_LOGI(TAG, "#6 %d", operateMode);
    sprintf(cmdStr, "#6 %d", operateMode);
    uart_write_bytes_with_break(EX_UART_NUM, cmdStr, strlen(cmdStr), 100);
    ESP_ERROR_CHECK(uart_wait_tx_done(EX_UART_NUM, 100));
}

void app_main(void)
{
    /* Initialize NVS */
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND)
    {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    vTaskDelay(2000 / portTICK_PERIOD_MS);
    uart_init();
    send_info();
    /* init wifi & connect */
    wifi_init();
    ota_init();
    time_init();
    send_mode();
    /* start usb camera*/
    uvc_streaming_init();
}
